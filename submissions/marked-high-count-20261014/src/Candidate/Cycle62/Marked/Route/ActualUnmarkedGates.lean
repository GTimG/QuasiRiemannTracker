import Candidate.Cycle62.Density.ActualBatchCount
import Candidate.Cycle62.Marked.Route.GenericCountAssembly

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Cycle62ActualUnmarked
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorInverseFiberCount HeckeDetectorRawFiber
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles HeckeDyadic
open LocalMoment

/-- The two unmarked gates for arbitrary legal cutoffs, uniformly in the
actual fixed dictionary, row population, height and dyadic fiber. -/
theorem actual_unmarked_fiber_gates {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (S : DensityCountingSetup)
    (εm : ℝ) (hεm : 0<εm) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀(a ε tstar T allowance height : ℝ)(i : ℕ),
      1/2≤a → 0≤ε → ε≤1/1000 → 1≤tstar → tstar≤3/2 →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀B : UnmarkedBatch Label U a ε tstar T allowance i,B.data=D.data →
      ∀label left right,∀hne : (B.fiberRows label left right).Nonempty,
      let F := B.fiber label left right hne
      (F.rows.card : ℝ)≤(192*(1+height)*(C*(1+height)^J))*
        U^(max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+2*ε+εm) ∧
      ∀j k : ℕ,j+k≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false
          ((logProfile^[j]) positiveAnnular) (U^F.m) σ freq*
          polynomial (F.family u F.label) false
          ((logProfile^[k]) positiveAnnular) (U^F.m) σ freq‖^2)≤
            (C*(1+height)^J)*U^(max 1 (2*F.m)+εm) := by
  let : NeZero S.modulus := ⟨S.nonzero⟩
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count S.modulus S.subgroup S.units
      S.exclusions S.profile S.smooth S.compact S.positiveSupport S.nonnegative S.nontrivial
      S.lower S.upper S.bound S.lowerPositive S.ordered S.boundPositive S.support S.bounded
      2 εm (by norm_num) hεm
  obtain ⟨J,C,hC,hmom⟩ := fixed_dictionary_actual_batch_moments D c κ εm hc hκ hεm hβ
  refine ⟨J,C*max 1 K₀,mul_pos hC (lt_of_lt_of_le zero_lt_one (le_max_left _ _)),?_⟩
  filter_upwards [hcount,hmom] with U hcount hmom
  refine ⟨hmom.1,?_⟩
  intro a ε tstar T allowance height i ha hε hε' ht ht' hh hf B hd label left right hne F
  have hm := hmom.2 ht ht' hε hε' B hd height hh label left right hne
  change UnmarkedMoments F c κ (C*(1+height)^J) height εm at hm
  have geom := fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i hmom.1
    F.witness F.left F.right F.fixed_left F.fixed_right
  change tstar-F.r-ε≤F.m ∧ F.r≤tstar+ε ∧ F.m≤1/2+75*ε ∧
    tstar-1/2-76*ε≤F.r ∧ 0≤F.m at geom
  have hr0 : 0≤F.r := by linarith [geom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [geom.2.1]
  have hi := hcount F.rows F.family a ε tstar T allowance i hmom.1 ha
    (fun u=>(F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
    F.fixed_right hr0 hr2 F.rowData F.reverse (C*(1+height)^J) height (by positivity) hh hf
    F.row_norm F.row_coeff hm.inverse_raw
  have hbase : C*(1+height)^J≤(C*max 1 K₀)*(1+height)^J := by
    have hhC : C≤C*max 1 K₀ := le_mul_of_one_le_right hC.le (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right hhC (by positivity)
  constructor
  · apply hi.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hmom.1).le _)
    have hcK : (C*(1+height)^J)*K₀≤(C*max 1 K₀)*(1+height)^J := by
      calc
        _≤(C*(1+height)^J)*max 1 K₀ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
        _=_ := by ring
    calc
      _≤(12*(1+height))*((C*max 1 K₀)*(1+height)^J) :=
        mul_le_mul_of_nonneg_left hcK (by positivity)
      _≤_ := mul_le_mul_of_nonneg_right (by nlinarith : 12*(1+height)≤192*(1+height))
        (by positivity)
  · intro j k hjk σ hσ freq hfreq
    exact (hm.plain_unmarked j k hjk σ hσ freq hfreq).trans
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (zero_lt_one.trans hmom.1).le _))

end OAI.SevenEighths.Cycle62ActualUnmarked
#print axioms OAI.SevenEighths.Cycle62ActualUnmarked.actual_unmarked_fiber_gates
