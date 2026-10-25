/- Copyright (c) 2026 Sil. Apache-2.0.
Finite complete extraction on an artificial divisor's support. All
valuations are retained, so the fifth-free restriction is not silently
replaced by an unshifted restriction after extracting one prime copy.
The finite expansion costs a subpower of the fixed support norm.
-/
import Candidate.Feedback.FourthPower.MixedCommonEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DivisorExtraction

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.MixedFixedSupport
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentSupport CenteredMomentCommonSectors CenteredMomentCommonAllocation
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open KernelIdeal
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem extract_dvd_fourth (I F : Id) (hI : I≠0) (hF : F≠0)
    (hf : SexticSieve.PowerFree 5 I) :
    supportExtract I (primeSupport F)∣F^4 := by
  apply (dvd_iff_valuation_le (supportExtract_ne_zero _ _) (pow_ne_zero 4 hF)).mpr
  intro P
  have he : valuation (supportExtract I (primeSupport F)) P=
      if P∈primeSupport F then valuation I P else 0 := supportExtract_count _ _ _
  rw [he,valuation_pow]
  by_cases hp : P∈primeSupport F
  · rw [ite_eq_left hp]
    have hv : 0<valuation F P := by
      change 0<(UniqueFactorizationMonoid.normalizedFactors F).count P
      exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    have hl := (powerFree_iff_valuations hI).mp hf P
    omega
  · simp only [ite_eq_right hp,Nat.zero_le]

def boundedLabels (S : ι→Finset Id) (F : Id) : Finset (ι→Id) :=
  (allocationLabels S F).filter (fun B=>∀j,B j∣F^4)

theorem active_extract_bounded (S : ι→Finset Id) (hS : ∀j,∀I∈S j,I≠0)
    (F : Id) (hF : F≠0) (c : (ι→Id)→ℂ)
    (hc : ∀v∈Fintype.piFinset S,c v≠0→SexticSieve.PowerFree 5 (∏j,v j))
    (v : ι→Id) (hv : v∈Fintype.piFinset S) (hn : c v≠0) :
    (fun j=>supportExtract (v j) (primeSupport F))∈boundedLabels S F := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,hv,rfl⟩,?_⟩
  intro j
  apply extract_dvd_fourth (v j) F (hS j _ (Fintype.mem_piFinset.mp hv j)) hF
  intro P hp hd
  exact hc v hv hn P hp (hd.trans (Finset.dvd_prod_of_mem v (Finset.mem_univ j)))

theorem bounded_fiber_sum (S : ι→Finset Id) (hS : ∀j,∀I∈S j,I≠0)
    (F : Id) (hF : F≠0) (c : (ι→Id)→ℂ)
    (hc : ∀v∈Fintype.piFinset S,c v≠0→SexticSieve.PowerFree 5 (∏j,v j)) :
    (∑v∈Fintype.piFinset S,c v)=
      ∑B∈boundedLabels S F,∑v∈sourceFiber S F B,c v := by
  rw [sum_source_fibers S F]
  symm
  apply Finset.sum_filter_of_ne
  intro B hB hn
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  have hb := (Finset.mem_filter.mp (active_extract_bounded S hS F hF c hc v hv hvn)).2
  simpa only [he] using hb

/-- A literal finite reindexing, valid with any phases in c. The only
support hypothesis is the already present fifth-free whole-column mask. -/
theorem bounded_residual_sum (S : ι→Finset Id) (hS : ∀j,∀I∈S j,I≠0)
    (F : Id) (hF : F≠0) (c : (ι→Id)→ℂ)
    (hc : ∀v∈Fintype.piFinset S,c v≠0→SexticSieve.PowerFree 5 (∏j,v j)) :
    (∑v∈Fintype.piFinset S,c v)=
      ∑B : boundedLabels S F,∑u∈residualBoxes S F B.val
        (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1,
          c (fun j=>B.val j*u j) := by
  rw [bounded_fiber_sum S hS F hF c hc]
  rw [←Finset.sum_coe_sort (boundedLabels S F)
    (fun B=>∑v∈sourceFiber S F B,c v)]
  apply Finset.sum_congr rfl
  intro B hB
  exact sourceFiber_sum S hS F hF B.val
    (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1
    (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).2 c

theorem bounded_labels_card (S : ι→Finset Id) (F : Id) (hF : F≠0) :
    (boundedLabels S F).card≤(idealDivisors (F^4)).card^(Fintype.card ι) := by
  let f (B : boundedLabels S F) : ι→idealDivisors (F^4) := fun j=>⟨B.val j,
    (mem_idealDivisors (pow_ne_zero 4 hF)).mpr ((Finset.mem_filter.mp B.property).2 j)⟩
  have hf : Function.Injective f := by
    intro B D he
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun he j)
  simpa only [Fintype.card_coe,Fintype.card_fun] using Fintype.card_le_of_injective f hf

theorem bounded_labels_subpower [Nonempty ι] (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀(S : ι→Finset Id)(F : Id),F≠0→
      ((boundedLabels S F).card:ℝ)≤K*(F.absNorm:ℝ)^ε := by
  have hn : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let δ := ε/(4*(Fintype.card ι:ℝ))
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨K,hK,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨K^(Fintype.card ι),pow_pos hK _,?_⟩
  intro S F hF
  have he : 4*(δ*(Fintype.card ι:ℝ))=ε := by dsimp only [δ];field_simp
  calc
    _ ≤ ((idealDivisors (F^4)).card:ℝ)^(Fintype.card ι) := by
      exact_mod_cast bounded_labels_card S F hF
    _ ≤ (K*((F^4).absNorm:ℝ)^δ)^(Fintype.card ι) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv (F^4) (pow_ne_zero 4 hF)) _
    _ = K^(Fintype.card ι)*(F.absNorm:ℝ)^ε := by
      rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      simp only [map_pow,Nat.cast_pow]
      rw [←Real.rpow_natCast_mul (Nat.cast_nonneg _)]
      norm_num only [Nat.cast_ofNat]
      rw [he]

/-- Divisibility by a supported prime is completely recorded in the
frozen factor. No local threshold or sign is discarded. -/
theorem supported_prime_dvd (P B u F : Id) (hP : Prime P)
    (hpF : P∣F) (hu : IsCoprime F u) : P∣B*u ↔ P∣B := by
  constructor
  · intro h
    rcases hP.dvd_mul.mp h with h|h
    · exact h
    · exact False.elim (hP.not_isUnit (hu.isUnit_of_dvd' hpF h))
  · exact fun h=>h.trans (dvd_mul_right B u)

omit [Fintype ι] in
theorem artificial_projector_frozen [DecidableEq ι]
    (D F : Id) (hDF : D∣F)
    (s : Finset ι) (a : Allocation D s) (B u : ι→Id)
    (hu : ∀j,IsCoprime F (u j)) :
    allocationTerm D s (fun j=>B j*u j) a=allocationTerm D s B a := by
  unfold allocationTerm
  apply Finset.prod_congr rfl
  intro P hP
  apply congrArg (fun z : ℂ=>(-1:ℂ)^((a P).val.card+1)*z)
  apply Finset.prod_congr rfl
  intro j hj
  have hpD : (P:Id)∣D :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp P.property)
  rw [supported_prime_dvd P (B j) (u j) F
    (IdealMobiusDivisorSum.support_prime P.property) (hpD.trans hDF) (hu j)]

end
end Candidate.Feedback.FourthPower.MixedFixedSupport
