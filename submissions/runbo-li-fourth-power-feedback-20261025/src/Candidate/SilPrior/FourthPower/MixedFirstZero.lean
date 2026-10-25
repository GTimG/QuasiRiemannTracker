/- Copyright (c) 2026 Sil. Apache-2.0.
The actual first-Poisson zero-frequency term from the baseline. For the
new fifth-free whole columns, its off-diagonal terms vanish exactly.
The remaining diagonal is bounded by the proved grouped square mass.
-/
import Candidate.SilPrior.FourthPower.MixedDiagonal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ZeroMode

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedFirstZero
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredExceptionalCount UniqueFactorizationMonoid CenteredMomentZeroMode
open CenteredMomentFourier CenteredMomentRowNorm ConcreteTraceCRT CubicEisenstein
open SexticSieve ReferenceConvolution MixedDiagonal
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem pair_zero_of_distinct (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (hfA : PowerFree 5 (Ideal.span {a}))
    (hfB : PowerFree 5 (Ideal.span {b})) (hne : Ideal.span {a} ≠ Ideal.span {b}) :
    pairFourier a b ha hb 0=0 := by
  by_contra hn
  apply hne
  apply (fifth_free_diagonal _ _ ha hb hfA hfB).mp
  intro P
  by_cases hP : P ∈ normalizedFactors ((Ideal.span {a})*(Ideal.span {b}))
  · obtain ⟨hmax,hgood,hodd⟩ := supported_factors_good _ ((supported_mul_iff _ _).mpr ⟨ha,hb⟩) P hP
    let := hmax
    exact valuation_profile_of_mean_ne_zero a b ha hb hn P hgood hodd
  · have hz : valuation ((Ideal.span {a})*(Ideal.span {b})) P=0 :=
      Multiset.count_eq_zero.mpr hP
    rw [valuation_mul _ _ _ ha.1 hb.1] at hz
    omega

def scaledMean (S : Finset Id) (hs : ∀ I ∈ S, Supported I) (K : ℝ) (I J : S) : ℂ :=
  (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖^2 : ℝ) : ℂ) *
    pairFourier (idealColumn S I) (idealColumn S J)
      (idealColumn_supported S hs I) (idealColumn_supported S hs J) 0)

theorem scaledMean_off_diagonal (S : Finset Id) (hs : ∀ I ∈ S, Supported I)
    (hf : ∀ I ∈ S, PowerFree 5 I) (K : ℝ) (I J : S) (hne : I ≠ J) :
    scaledMean S hs K I J=0 := by
  unfold scaledMean
  rw [pair_zero_of_distinct _ _ _ _
    (by rw [idealColumn_span]; exact hf I.val I.property)
    (by rw [idealColumn_span]; exact hf J.val J.property)
    (by rw [idealColumn_span,idealColumn_span]; exact fun he => hne (Subtype.ext he)),mul_zero]

theorem zero_energy_diagonal (S : Finset Id) (hs : ∀ I ∈ S, Supported I)
    (hf : ∀ I ∈ S, PowerFree 5 I) (c : Id → ℂ) (K : ℝ) :
    idealZeroEnergy S hs c K = ∑ I : S, (c I.val*star (c I.val))*scaledMean S hs K I I := by
  unfold idealZeroEnergy
  apply Finset.sum_congr rfl
  intro I _
  change (∑ J : S, (c I.val*star (c J.val))*scaledMean S hs K I J) = _
  rw [Finset.sum_eq_single I]
  · intro J _ hJI
    rw [scaledMean_off_diagonal S hs hf K I J (Ne.symm hJI),mul_zero]
  · simp

theorem zero_energy_mass (S : Finset Id) (hs : ∀ I ∈ S, Supported I)
    (hf : ∀ I ∈ S, PowerFree 5 I) (c : Id → ℂ) (K : ℝ) (hK : 0 ≤ K) :
    ‖idealZeroEnergy S hs c K‖ ≤ K*coefficientMass S c := by
  rw [zero_energy_diagonal S hs hf c K]
  calc
    _ ≤ ∑ I : S, ‖(c I.val*star (c I.val))*scaledMean S hs K I I‖ := norm_sum_le _ _
    _ ≤ ∑ I : S, ‖c I.val‖^2*K := by
      apply Finset.sum_le_sum
      intro I _
      rw [norm_mul,norm_mul,norm_star,← pow_two]
      exact mul_le_mul_of_nonneg_left
        (scaled_zero_mean_norm_le _ _ _ _ K hK) (sq_nonneg _)
    _ = K*coefficientMass S c := by
      rw [← Finset.sum_mul,Finset.sum_coe_sort S (fun I : Id => ‖c I‖^2)]
      exact mul_comm _ _

variable {ι : Type*} [Fintype ι]

theorem grouped_first_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ι → Id)) (β : (ι → Id) → ℂ) (N B K : ℝ),
      1 ≤ N → 0 ≤ B → 0 ≤ K →
      (∀ v ∈ S, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S, PowerFree 5 (product v)) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      ∀ hs : ∀ I ∈ columns S, Supported I,
      ‖idealZeroEnergy (columns S) hs (coefficient S β) K‖ ≤ C*K*N^ε*B^2 := by
  obtain ⟨C,hC,hb⟩ := grouped_mass (ι := ι) ε hε
  refine ⟨C,hC,?_⟩
  intro S β N B K hN hB hK hgeom hf hβ hs
  have hf' (I : Id) (hi : I ∈ columns S) : PowerFree 5 I := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
    exact hf v hv
  calc
    _ ≤ K*coefficientMass (columns S) (coefficient S β) :=
      zero_energy_mass (columns S) hs hf' (coefficient S β) K hK
    _ ≤ K*(C*N^ε*B^2) := mul_le_mul_of_nonneg_left (hb S β N B hN hB hgeom hβ) hK
    _ = _ := by ring

end
end Candidate.SilPrior.FourthPower.MixedFirstZero
