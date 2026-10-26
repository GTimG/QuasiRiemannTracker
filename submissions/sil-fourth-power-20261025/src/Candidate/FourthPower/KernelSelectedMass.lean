/- Copyright (c) 2026 Sil. Apache-2.0.
Absolute mass for the actual prime-dependent kernelOn, with each supplying
prime occupied by exactly one frozen label. No ordinary kernel is inserted
at a supplying prime. Positive Euler factors only enlarge its majorant.
-/
import Candidate.FourthPower.KernelRowProfiles
import Candidate.FourthPower.KernelInverseSlotMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelSelectedMass
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelLabelledSlots KernelIdealMass
open SieveDescent SieveCentralReference
local notation "Id" => Ideal ActualEisensteinCubic.O

def localWeight (A : LocalSeries) (s t : ℝ) (P : PrimeIdeal) (ij : ℕ × ℕ) : ℝ :=
  |((MvPowerSeries.coeff (exponent ij.1 ij.2) A : ℤ) : ℝ)| *
    ((Ideal.absNorm P.val : ℝ)^(-s))^ij.1*((Ideal.absNorm P.val : ℝ)^(-t))^ij.2

theorem localWeight_nonneg (A : LocalSeries) (s t : ℝ) (P : PrimeIdeal) (ij : ℕ × ℕ) :
    0 ≤ localWeight A s t P ij := by unfold localWeight; positivity

def idealWeight (S : Finset PrimeIdeal) (A : S → LocalSeries) (s t : ℝ) (d : Id × Id) : ℝ :=
  |(kernelOn S A d.1 d.2 : ℝ)| * normWeight s d.1 * normWeight t d.2

theorem idealWeight_nonneg (S : Finset PrimeIdeal) (A : S → LocalSeries)
    (s t : ℝ) (d : Id × Id) : 0 ≤ idealWeight S A s t d := by
  unfold idealWeight normWeight
  positivity

theorem idealWeight_product (S : Finset PrimeIdeal) (A : S → LocalSeries)
    (s t : ℝ) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : pairSupport d.1 d.2 ⊆ primeValues S) :
    idealWeight S A s t d = ∏ P : S, localWeight (A P) s t P.val (encodePair S d P) := by
  unfold idealWeight kernelOn
  rw [normWeight_prime_product s hd.1 S (Finset.Subset.trans Finset.subset_union_left hs),
    normWeight_prime_product t hd.2 S (Finset.Subset.trans Finset.subset_union_right hs)]
  push_cast
  rw [Finset.abs_prod,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  rfl

/-- Prime-dependent finite Euler domination. Marked constant coefficients may
vanish, and no artificial constant-one hypothesis is imposed on the series. -/
theorem finite_ideal_product (S : Finset PrimeIdeal) (A : S → LocalSeries)
    (s t : ℝ) (D : Finset (Id × Id))
    (hd : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    (∑ d ∈ D, idealWeight S A s t d) ≤
      ∏ P : S, ∑ ij ∈ D.image (fun d => encodePair S d P), localWeight (A P) s t P.val ij := by
  let enc : D → S → ℕ × ℕ := fun d => encodePair S d.val
  let T : S → Finset (ℕ × ℕ) := fun P => D.image (fun d => encodePair S d P)
  have hinj : Function.Injective enc := by
    intro d e he
    exact Subtype.ext (encodePair_injective (hd d.val d.property) (hd e.val e.property)
      (hs d.val d.property) (hs e.val e.property) he)
  have hsub : Finset.univ.image enc ⊆ Fintype.piFinset T := by
    intro a ha
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp ha
    exact Fintype.mem_piFinset.mpr (fun P => Finset.mem_image.mpr ⟨d.val,d.property,rfl⟩)
  rw [← Finset.sum_coe_sort D (idealWeight S A s t)]
  calc
    _ = ∑ a ∈ Finset.univ.image enc, ∏ P : S, localWeight (A P) s t P.val (a P) := by
      rw [Finset.sum_image (fun d _ e _ h => hinj h)]
      exact Finset.sum_congr rfl (fun d _ => idealWeight_product S A s t d.val
        (hd d.val d.property) (hs d.val d.property))
    _ ≤ ∑ a ∈ Fintype.piFinset T, ∏ P : S, localWeight (A P) s t P.val (a P) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun a _ _ => Finset.prod_nonneg (fun P _ => localWeight_nonneg _ _ _ _ _))
    _ = _ := (Finset.prod_univ_sum T (fun P : S => localWeight (A P) s t P.val)).symm

variable {α : Type*} [Fintype α]

theorem selected_product (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (w : S → ℝ) :
    (∏ P : S, if marked S slot P then w P else 1) = ∏ i : α, w (slot i) := by
  let image := Finset.univ.image slot
  have he : ∀ P : S, (marked S slot P=true) ↔ P ∈ image := by
    intro P
    simp [marked,frozen,image]
  simp_rw [he]
  rw [← Finset.prod_filter]
  have hf : (Finset.univ.filter (fun P : S => P ∈ image)) = image := by ext P; simp
  rw [hf,Finset.prod_image (fun i _ j _ h => hinj h)]

/-- Local marked mass replaces the ordinary factor at each supplying prime.
All additional allocation restrictions may be imposed through the finite D. -/
theorem selected_ideal_mass (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (A B : LocalSeries) (s t : ℝ)
    (ordinary markedMass z : S → ℝ)
    (ho : ∀ P, 1 ≤ ordinary P) (hm : ∀ P, 0 ≤ markedMass P) (hz : ∀ P, 0 ≤ z P)
    (hA : ∀ P : S, ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight A s t P.val ij) ≤ ordinary P)
    (hB : ∀ P : S, ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight B s t P.val ij) ≤ markedMass P)
    (D : Finset (Id × Id)) (hd : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    (∑ d ∈ D, idealWeight S (fun P => if marked S slot P then B else A) s t d)*
      (∏ i : α, z (slot i)) ≤ (∏ P : S, ordinary P)*
        ∏ i : α, markedMass (slot i)*z (slot i) := by
  have hloc (P : S) :
      (∑ ij ∈ D.image (fun d => encodePair S d P),
        localWeight (if marked S slot P then B else A) s t P.val ij) ≤
      ordinary P*(if marked S slot P then markedMass P else 1) := by
    split_ifs with h
    · exact (hB P _).trans (le_mul_of_one_le_left (hm P) (ho P))
    · simpa only [mul_one] using hA P (D.image (fun d => encodePair S d P))
  have hbase : (∑ d ∈ D, idealWeight S (fun P => if marked S slot P then B else A) s t d) ≤
      (∏ P : S, ordinary P)*(∏ i : α, markedMass (slot i)) := by
    apply (finite_ideal_product S _ s t D hd hs).trans
    calc
      _ ≤ ∏ P : S, ordinary P*(if marked S slot P then markedMass P else 1) :=
        Finset.prod_le_prod₀ (fun P _ => Finset.sum_nonneg
          (fun ij _ => localWeight_nonneg _ _ _ _ _)) (fun P _ => hloc P)
      _ = _ := by rw [Finset.prod_mul_distrib,selected_product S slot hinj]
  calc
    _ ≤ ((∏ P : S, ordinary P)*(∏ i : α, markedMass (slot i)))*(∏ i : α, z (slot i)) :=
      mul_le_mul_of_nonneg_right hbase (Finset.prod_nonneg (fun i _ => hz (slot i)))
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

/-- A fixed labelled family of harmonic prime weights costs only X^epsilon.
The constant is selected before the prime pool, coefficients, or cutoffs. -/
theorem prime_assignments_subpower (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      (∑ slot : α → S, ∏ i : α, K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹) ≤ C*X^ε := by
  let δ := ε/((Fintype.card α : ℝ)+1)
  have hd : 0 < (Fintype.card α : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hd
  let B := K*rootMass (1+δ)
  have hB : 0 ≤ B := mul_nonneg hK (rootMass_nonneg _)
  refine ⟨(B+1)^Fintype.card α,by positivity,?_⟩
  intro X hX S hS
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hsum : (∑ P : S, K*(Ideal.absNorm P.val.val : ℝ)⁻¹) ≤ B*X^δ := by
    rw [← Finset.mul_sum]
    have he : (∑ P : S, (Ideal.absNorm P.val.val : ℝ)⁻¹) =
        ∑ P ∈ primeValues S, (Ideal.absNorm P : ℝ)⁻¹ := by
      unfold primeValues
      rw [Finset.sum_image (by intro P _ Q _ h; exact Subtype.val_injective h)]
      exact Finset.sum_coe_sort S (fun P : PrimeIdeal => (Ideal.absNorm P.val : ℝ)⁻¹)
    rw [he]
    have h := mul_le_mul_of_nonneg_left (reciprocal_mass δ hδ X hX0 (primeValues S) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
      exact hS Q hQ)) hK
    convert h using 1
    dsimp only [B]
    ring
  have he : δ*(Fintype.card α : ℝ) ≤ ε := by
    have hh : δ*((Fintype.card α : ℝ)+1)=ε := div_mul_cancel₀ ε (ne_of_gt hd)
    nlinarith
  calc
    _ = ∏ _i : α, ∑ P : S, K*(Ideal.absNorm P.val.val : ℝ)⁻¹ :=
      (Fintype.prod_sum (fun _i : α => fun P : S => K*(Ideal.absNorm P.val.val : ℝ)⁻¹)).symm
    _ ≤ ∏ _i : α, B*X^δ := Finset.prod_le_prod₀
      (fun _ _ => Finset.sum_nonneg (fun P _ => by positivity)) (fun _ _ => hsum)
    _ = B^Fintype.card α*X^(δ*(Fintype.card α : ℝ)) := by
      rw [Finset.prod_const,Finset.card_univ,mul_pow,
        ← Real.rpow_natCast (X^δ) (Fintype.card α),← Real.rpow_mul hX0.le]
    _ ≤ (B+1)^Fintype.card α*X^ε := mul_le_mul
      (pow_le_pow_left₀ hB (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hX he) (by positivity) (by positivity)

end
end Candidate.FourthPower.KernelSelectedMass
