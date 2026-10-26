import Candidate.Cycle63.Moment.FirstSourceEncoding
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RankinLabels

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentRankinLabels
open Cycle63Moment
local notation "O" => HeckeFamily.O

def firstPartitionCode (l : FirstSourceLabel) : (Ideal O×Ideal O)×Finset (Ideal O) :=
  (l.1,l.2.val.image Subtype.val)

theorem first_partition_code_injective : Function.Injective firstPartitionCode := by
  rintro ⟨CD,E⟩ ⟨CD',F⟩ h
  have hCD : CD=CD' := congrArg Prod.fst h
  cases hCD
  have hEF : E.val=F.val := Finset.image_injective Subtype.val_injective (congrArg Prod.snd h)
  have he : E=F := Subtype.ext hEF
  cases he
  rfl

/-- The low branch may count first labels explicitly. The inactive subset
is included, arbitrary valuations are allowed, and the old seed is saved. -/
theorem actual_first_low_label_count (B ε : ℝ)(hB : 0≤B)(hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀Z : ℝ,1≤Z → ∀p : ℝ,p≤B →
      ∀(seed : Ideal O),Squarefree seed → seed≠0 → ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤Z^p) →
      (labels.card:ℝ)≤K*Z^(p+ε)/(seed.absNorm:ℝ) := by
  let e := ε/(3*B+1)
  have he : 0<e := div_pos hε (by positivity)
  obtain ⟨K,hK,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨K,hK,?_⟩
  intro Z hZ p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hz := zero_lt_one.trans_le hZ
  have hpart (l : FirstSourceLabel) :
      (firstPartitionCode l).2⊆IdealMobiusDivisorSum.primeSupport (commonRadical l.1.1 l.1.2) := by
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    rw [commonRadical_support]
    exact Q.property
  have hh := hcount seed hs hs0 (labels.image firstPartitionCode)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact ⟨(hsup l hl).1.1,(hsup l hl).2.1⟩)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact heq l hl)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact hseed l hl)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact hpart l)
    (Z^B) (Z^B) (Z^p) (Real.rpow_pos_of_pos hz _) (Real.rpow_pos_of_pos hz _)
    (Real.rpow_pos_of_pos hz _)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact hnorm l hl)
    (by intro v hv;obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv;exact hrad l hl)
  rw [Finset.card_image_of_injective _ first_partition_code_injective] at hh
  have hexp : B*e+B*e+p*(1+e)≤p+ε := by
    have hid : e*(3*B+1)=ε := by dsimp only [e];field_simp
    nlinarith [mul_le_mul_of_nonneg_right hp he.le]
  calc
    _≤K*(Z^B)^e*(Z^B)^e*(Z^p)^(1+e)/(seed.absNorm:ℝ) := hh
    _=K*Z^(B*e+B*e+p*(1+e))/(seed.absNorm:ℝ) := by
      simp only [←Real.rpow_mul hz.le,Real.rpow_add hz]
      ring
    _≤_ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) hK.le)
      (Nat.cast_nonneg _)

end
end OAI.SevenEighths.Cycle63InitialMass
