import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointHighDensity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open Cycle63Moment CenteredMomentFirstAmplificationChoice CenteredMomentAbsoluteEnergy
open CenteredMomentSectorLocalization ConcreteTraceCRT QuadraticInitialBound
local notation "O" => HeckeFamily.O

/-- A fixed smooth majorant counts all literal lattice rows, independently of
zero detection or Mellin height. -/
theorem coarse_nonzero_lattice_count (X : ℝ)(hX : 1≤X)
    (rows : Finset NonzeroFrequency)
    (hrows : ∀w∈rows,rawFrequencyNorm w≤X) :
    (rows.card:ℝ)≤diagonalControl ballProfile*X := by
  have hX0 : 0<X := by linarith
  let vals := rows.image (fun w=>w.val)
  have hcard : vals.card=rows.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hpoint (z : O)(hz : z∈vals) :
      1≤‖ballProfile (‖eisEmbedding z‖^2/X)‖ := by
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact (ballProfile_majorizes X hX0 w.val (hrows w hw)).trans (Complex.re_le_norm _)
  calc
    (rows.card:ℝ) = ∑ _z∈vals,(1:ℝ) := by simp [hcard]
    _ ≤ ∑ z∈vals,‖ballProfile (‖eisEmbedding z‖^2/X)‖ := Finset.sum_le_sum hpoint
    _ ≤ ∑' z : O,‖ballProfile (‖eisEmbedding z‖^2/X)‖ :=
      (radial_norm_summable ballProfile X hX0).sum_le_tsum vals (fun _ _=>norm_nonneg _)
    _ ≤ _ := by simpa only [max_eq_right hX] using radial_weight_lattice_bound_all ballProfile X hX0

/-- Coarse joint cardinality, retaining the same missing-radical fiber count
as the sharp high branch. All constants precede labels and moving data. -/
theorem actual_joint_coarse_row_count (B loss : ℝ)(hB : 0≤B)(hloss : 0<loss) :
    ∃C : ℝ,0<C ∧ ∀left : Bool,∀u₀ : O,∀unit : FirstSourceLabel→O,
      ∀Z : ℝ,2≤Z → ∀m : ℝ,
      ∀labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      (∀label∈labels,rawFrequencyNorm (nonzeroJointSourceRow label)≤Z^B) →
      (∀label∈labels,Supported label.val.1.1.1 ∧ label.val.1.1.2≠0 ∧
        Supported label.val.2.1.1 ∧ label.val.2.1.2≠0) →
      (∀label∈labels,primeSupport label.val.1.1.1=primeSupport label.val.1.1.2 ∧
        primeSupport label.val.2.1.1=primeSupport label.val.2.1.2) →
      (∀label∈labels,((Ideal.span {jointSourceRow left u₀ unit label.val}*
        firstSourceMissing left label.val.1).absNorm:ℝ)≤Z^B) →
      (∀label∈labels,(label.val.1.1.1.absNorm:ℝ)≤Z^B ∧
        (label.val.1.1.2.absNorm:ℝ)≤Z^B ∧
        (label.val.2.1.1.absNorm:ℝ)≤Z^B ∧ (label.val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀label∈labels,((firstSourceMissing left label.val.1).absNorm:ℝ)≤Z^m) →
      (labels.card:ℝ)≤C*Z^(m+B+loss) := by
  obtain ⟨C,hC,hfiber⟩ := nonzero_joint_source_fiber_count B loss hB hloss
  let D := max 1 (diagonalControl ballProfile)
  have hD : 0<D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro left u₀ unit Z hZ m labels hrowbound hnonzero heq hsupportnorm hnorm hmissing
  have hZ0 : 0<Z := by linarith
  have hd : ((labels.image nonzeroJointSourceRow).card:ℝ)≤D*Z^B := by
    apply (coarse_nonzero_lattice_count (Z^B)
      (Real.one_le_rpow (by linarith) hB) (labels.image nonzeroJointSourceRow) ?_).trans
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    · intro w hw
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hw
      exact hrowbound l hl
  calc (labels.card:ℝ)
      ≤ ((labels.image nonzeroJointSourceRow).card:ℝ)*(C*Z^(m+loss)) :=
        card_le_image_card_mul _ labels _ (fun w _ =>
          hfiber left u₀ unit Z hZ m labels hrowbound hnonzero heq hsupportnorm hnorm hmissing w)
    _ ≤ (D*Z^B)*(C*Z^(m+loss)) := mul_le_mul_of_nonneg_right hd (by positivity)
    _ = (D*C)*Z^(m+B+loss) := by
      calc
        _ = (D*C)*(Z^B*Z^(m+loss)) := by ring
        _ = _ := by rw [←Real.rpow_add hZ0]; congr 1; ring_nf
end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
