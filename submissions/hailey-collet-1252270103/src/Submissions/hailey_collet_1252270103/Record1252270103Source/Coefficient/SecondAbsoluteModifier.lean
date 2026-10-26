/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal correction is bounded on every stored tuple, including padded
zero tuples. The bound uses the full stored-column cap, before coefficient
or complete-row nonzero filtering. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.SecondRemainder.Correction
import Submissions.hailey_collet_1252270103.Record1252270103Source.Pool.FixedCell

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.SecondAbsoluteEnvelope
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic
open Record1252270103Source QRH.Record1252270103Low SecondRemainder
local notation "O" => ActualEisensteinCubic.O
local instance absoluteModifierTupleDecidable {κ : Type*} :
    DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- Full-pool correction bound. A zero stored column has correction zero;
nonzero columns use the actual prime-divisor count. -/
theorem corrected_one_full_pool {ι : Type*} [Fintype ι]
    (s : Input ι) (A₁ A₂ D K : Ideal O)
    (P : Finset (Ideal O)) (hP : P.Nonempty) (hp : ∀p∈P,Prime p)
    (Z ell B : ℝ) (hZ : 1<Z) (hell : 0<ell)
    (hlower : ∀p∈P,Z^ell≤(p.absNorm:ℝ))
    (hsize : 2*(B/ell)≤(P.card:ℝ))
    (hpool : ∀I∈finiteColumns (Fintype.piFinset s.pools),
      (I.absNorm:ℝ)≤Z^B) :
    ∀v∈Fintype.piFinset s.pools,
      ‖correctedModifier P A₁ A₂ D K (fun _=>1) v‖≤2 := by
  intro v hv
  apply marked_modifier_norm_le A₁ A₂ 1 K _ v 2 (by norm_num)
  simp only [one_mul,mul_one]
  by_cases hI : finiteTupleProduct v=0
  · simp [hI,idealDividingPool]
  · exact correction_norm_le_two P hP hp (finiteTupleProduct v) hI
      Z ell B hZ hell hlower
      (hpool _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)) hsize

/-- The same fixed-cell pool supplies all counting hypotheses. In the
initial-family caller the stored-column exponent Bsource is four. -/
theorem fixed_cell_corrected_one_full_pool {ι : Type*} [Fintype ι]
    (s : Input ι) (A₁ A₂ D K : Ideal O)
    (P : Finset (Ideal O)) (Z a ell mesh loss BD Bsource : ℝ) (depth : ℕ)
    (hcell : Pool.FixedCellPoolData P Z a ell mesh loss BD Bsource depth)
    (hell : 0<ell)
    (hpool : ∀I∈finiteColumns (Fintype.piFinset s.pools),
      (I.absNorm:ℝ)≤Z^Bsource) :
    ∀v∈Fintype.piFinset s.pools,
      ‖correctedModifier P A₁ A₂ D K (fun _=>1) v‖≤2 :=
  corrected_one_full_pool s A₁ A₂ D K P hcell.nonempty hcell.prime
    Z ell Bsource hcell.scale_gt_one hell hcell.norm_lower hcell.card_source hpool

end
end QRH.Record1252270103Source.SecondAbsoluteEnvelope

#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.corrected_one_full_pool
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.fixed_cell_corrected_one_full_pool
