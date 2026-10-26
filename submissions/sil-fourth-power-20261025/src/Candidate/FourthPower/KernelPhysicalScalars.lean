/- Copyright (c) 2026 Sil. Apache-2.0.
The actual natural-slot and whole-character scalars of physical restoration,
including the critical reflected ratio. Phases stay outside residual norms.
-/
import Candidate.FourthPower.KernelActualMass
import Candidate.FourthPower.KernelNaturalSlots

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelPhysicalScalars
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelLabelledSlots KernelSelectedMass KernelActualMass
open KernelRowProfiles KernelNaturalSlots
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

theorem extracted_central_bound (χ : Character) (S : Finset PrimeIdeal) (A : S → LocalSeries)
    (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    ‖extractedScalar χ (fun e => (kernelOn S A e.1 e.2 : ℂ)) d‖ ≤
      idealWeight S A (1/2) (1/2) d := by
  have hi : (0 : ℝ) < Ideal.absNorm d.1 := zero_lt_one.trans_le (ideal_norm_one_le hd.1)
  have hj : (0 : ℝ) < Ideal.absNorm d.2 := zero_lt_one.trans_le (ideal_norm_one_le hd.2)
  have he : (Real.sqrt (pairNorm d))⁻¹=normWeight (1/2) d.1*normWeight (1/2) d.2 := by
    rw [pairNorm,Real.sqrt_mul hi.le,mul_inv_rev]
    unfold normWeight
    rw [Real.rpow_neg hi.le,Real.rpow_neg hj.le,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow]
    ring
  apply (extractedScalar_bound χ (fun e => (kernelOn S A e.1 e.2 : ℂ)) d).trans_eq
  rw [div_eq_mul_inv,he]
  unfold idealWeight
  rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  ring

def scalar (χ : Character) (S : Finset PrimeIdeal) (A B : LocalSeries)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ) (slot : α → S) (d : Id × Id) : ℂ :=
  extractedScalar χ
    (fun e => (kernelOn S (fun Q => if marked S slot Q then B else A) e.1 e.2 : ℂ)) d *
      ∏ i : α, slotTerm χ (pool i) (β i) (P i) (slot i).val.val

theorem scalar_bound (χ : Character) (S : Finset PrimeIdeal) (A B : LocalSeries)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hP : ∀ i, 0 < P i)
    (hp : ∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i)
    (hβ : ∀ i I, I ∈ pool i → ‖β i I‖ ≤ M)
    (slot : α → S) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    ‖scalar χ S A B pool β P slot d‖ ≤
      (2*M)^Fintype.card α*frozenMass S A B (1/2) (1/2) (1/2) slot d := by
  have hs : ‖∏ i : α, slotTerm χ (pool i) (β i) (P i) (slot i).val.val‖ ≤
      (2*M)^Fintype.card α*∏ i : α, normWeight (1/2) (slot i).val.val := by
    rw [norm_prod]
    calc
      _ ≤ ∏ i : α, (2*M)*normWeight (1/2) (slot i).val.val :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ =>
          slotTerm_bound χ (pool i) (β i) (P i) M (hP i) hM (hp i) (hβ i) (slot i).val.val)
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  unfold scalar
  rw [norm_mul]
  apply (mul_le_mul (extracted_central_bound χ S _ d hd) hs (norm_nonneg _)
    (idealWeight_nonneg _ _ _ _ _)).trans_eq
  unfold frozenMass
  ring

def frozenNorm (S : Finset PrimeIdeal) (slot : α → S) : ℝ :=
  ∏ i : α, (Ideal.absNorm (slot i).val.val : ℝ)

theorem frozenNorm_pos (S : Finset PrimeIdeal) (slot : α → S) : 0 < frozenNorm S slot :=
  Finset.prod_pos (fun i _ => zero_lt_one.trans_le (ideal_norm_one_le (slot i).val.property.ne_zero))

def criticalRatio (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) : ℝ :=
  ((Ideal.absNorm d.2 : ℝ)/((Ideal.absNorm d.1 : ℝ)*frozenNorm S slot))^(1/6 : ℝ)

theorem criticalRatio_nonneg (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) :
    0 ≤ criticalRatio S slot d := by unfold criticalRatio frozenNorm; positivity

/-- The ratio uses the norm of the whole frozen product, including every
marked factor. Its exact exponents are the ones in ForwardCriticalMass. -/
theorem reflected_weight (S : Finset PrimeIdeal) (slot : α → S)
    (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    ForwardCentralMass S slot d*criticalRatio S slot d = ForwardCriticalMass S slot d := by
  have hx : (0 : ℝ) < Ideal.absNorm d.1 := zero_lt_one.trans_le (ideal_norm_one_le hd.1)
  have hy : (0 : ℝ) < Ideal.absNorm d.2 := zero_lt_one.trans_le (ideal_norm_one_le hd.2)
  have hq (i : α) : (0 : ℝ) < Ideal.absNorm (slot i).val.val :=
    zero_lt_one.trans_le (ideal_norm_one_le (slot i).val.property.ne_zero)
  have hr : criticalRatio S slot d =
      ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/6 : ℝ)*
        ∏ i : α, (Ideal.absNorm (slot i).val.val : ℝ)^(-(1/6 : ℝ)) := by
    unfold criticalRatio
    rw [← div_div,Real.div_rpow (div_pos hy hx).le (frozenNorm_pos S slot).le,
      div_eq_mul_inv,← Real.rpow_neg (frozenNorm_pos S slot).le]
    unfold frozenNorm
    rw [← Real.finsetProd_rpow Finset.univ _ (fun i _ => (hq i).le)]
  have hprod : (∏ i : α, normWeight (1/2) (slot i).val.val)*
      (∏ i : α, (Ideal.absNorm (slot i).val.val : ℝ)^(-(1/6 : ℝ))) =
        ∏ i : α, normWeight (2/3) (slot i).val.val := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    unfold normWeight
    rw [← Real.rpow_add (hq i)]
    congr 1
    norm_num
  have hdw : normWeight (1/2) d.1*normWeight (1/2) d.2*
      ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/6 : ℝ) =
        normWeight (2/3) d.1*normWeight (1/3) d.2 :=
    KernelReflectedMass.central_ratio _ _ hx hy
  unfold ForwardCentralMass ForwardCriticalMass frozenMass idealWeight
  rw [hr]
  calc
    _ = |(kernelOn S (fun Q => if marked S slot Q then
        LocalKernels.base formalX formalY-kernelSeries else kernelSeries) d.1 d.2 : ℝ)| *
        (normWeight (1/2) d.1*normWeight (1/2) d.2*
          ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/6 : ℝ)) *
        ((∏ i : α, normWeight (1/2) (slot i).val.val)*
          (∏ i : α, (Ideal.absNorm (slot i).val.val : ℝ)^(-(1/6 : ℝ)))) := by ring
    _ = _ := by rw [hdw,hprod]; ring

def ordinarySeriesFor (inv : Bool) : LocalSeries := if inv then reciprocalSeries else kernelSeries
def markedSeriesFor (inv : Bool) : LocalSeries :=
  if inv then KernelInverseMarkedMass.markedSeries else LocalKernels.base formalX formalY-kernelSeries

/-- Actual normalized coefficients, not a model coefficient system. The bound
is uniform over the physical character, its zeros, original annuli and profiles. -/
theorem natural_scalar_mass (inv : Bool) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      ∀ (χ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      (∑ slot ∈ F, ∑ d ∈ D slot,
        ‖scalar χ S (ordinarySeriesFor inv) (markedSeriesFor inv) pool β P slot d‖) ≤ C*X^ε := by
  have hm : ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot,
        frozenMass S (ordinarySeriesFor inv) (markedSeriesFor inv) (1/2) (1/2) (1/2) slot d) ≤ M*X^ε := by
    cases inv
    · exact forward_central_subpower ε hε
    · exact inverse_central_subpower ε hε
  obtain ⟨M,hM,hbound⟩ := hm
  refine ⟨(2*B+1)^Fintype.card α*M,mul_pos (by positivity) hM,?_⟩
  intro X hX S hS F hinj D hd hs χ pool β P hP hp hβ
  calc
    _ ≤ ∑ slot ∈ F, ∑ d ∈ D slot, (2*B)^Fintype.card α *
        frozenMass S (ordinarySeriesFor inv) (markedSeriesFor inv) (1/2) (1/2) (1/2) slot d :=
      Finset.sum_le_sum (fun slot hslot => Finset.sum_le_sum (fun d hdd =>
        scalar_bound χ S _ _ pool β P B hB hP hp hβ slot d (hd slot hslot d hdd)))
    _ = (2*B)^Fintype.card α*(∑ slot ∈ F, ∑ d ∈ D slot,
        frozenMass S (ordinarySeriesFor inv) (markedSeriesFor inv) (1/2) (1/2) (1/2) slot d) := by
      simp_rw [← Finset.mul_sum]
    _ ≤ (2*B)^Fintype.card α*(M*X^ε) :=
      mul_le_mul_of_nonneg_left (hbound X hX S hS F hinj D hd hs) (by positivity)
    _ ≤ ((2*B+1)^Fintype.card α*M)*X^ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (mul_nonneg hM.le (Real.rpow_nonneg (zero_le_one.trans hX) _))

end
end Candidate.FourthPower.KernelPhysicalScalars
