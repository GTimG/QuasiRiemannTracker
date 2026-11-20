/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairPhysical

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

lemma finite_good_expansion {α : Type*} (S : Finset α) (f : α → ℂ) (g : α → Fin 7 → ℂ) :
    (∏ P ∈ S,(f P+∑ j : Fin 7,g P j)) =
      ∑ T ∈ S.powerset, ∑ k : T → Fin 7,
        (∏ P : T,g P.val (k P))*(∏ P ∈ S \ T,f P) := by
  rw [show (∏ P ∈ S,(f P+∑ j : Fin 7,g P j))=
      ∏ P ∈ S,((∑ j : Fin 7,g P j)+f P) from Finset.prod_congr rfl (fun _ _ => add_comm _ _),
    Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T _
  rw [←Finset.prod_coe_sort T,Fintype.prod_sum,Finset.sum_mul]

lemma finite_exceptional_expansion {α : Type*} (bad : Finset α)
    (allowed : α → Finset (ℕ×ℕ)) (g : (P : bad) → allowed P.val → Fin 4 → ℂ) :
    (∏ P : bad, ∑ q : allowed P.val, ∑ j : Fin 4,g P q j) =
      ∑ q : (P : bad) → allowed P.val, ∑ j : bad → Fin 4,
        ∏ P : bad,g P (q P) (j P) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact Fintype.prod_sum _

def ordinaryLocalCoefficient (χ₁ χ₂ : Character) (a b : PrimeIdeal → ℕ) (P : PrimeIdeal) : ℂ :=
  (idealCoeff χ₁ P.val)^a P*(idealCoeff χ₂ P.val)^b P

def goodPrimeKernel (χ₁ χ₂ ψ₁ ψ₂ : Character) (a b : PrimeIdeal → ℕ)
    (P : PrimeIdeal) (j : Fin 7) : ℂ :=
  if (h3Exponent j).1 ≤ a P ∧ (h3Exponent j).2 ≤ b P then
    h3Term (idealCoeff ψ₁ P.val) (idealCoeff ψ₂ P.val) j*
      (idealCoeff χ₁ P.val)^(a P-(h3Exponent j).1)*
      (idealCoeff χ₂ P.val)^(b P-(h3Exponent j).2) else 0

def exceptionalPrimeKernel (χ₁ χ₂ ψ₁ ψ₂ : Character) (a b : PrimeIdeal → ℕ)
    (P : PrimeIdeal) (q : ℕ×ℕ) (j : Fin 4) : ℂ :=
  if q.1+deletionExponent₁ j ≤ a P ∧ q.2+deletionExponent₂ j ≤ b P then
    ((idealCoeff ψ₁ P.val)^q.1*(idealCoeff ψ₂ P.val)^q.2)*
      deletionTerm (idealCoeff χ₁ P.val) (idealCoeff χ₂ P.val) j*
      (idealCoeff χ₁ P.val)^(a P-q.1-deletionExponent₁ j)*
      (idealCoeff χ₂ P.val)^(b P-q.2-deletionExponent₂ j) else 0

/-- The finite extraction uses the existing good-prime numerator index. The
ordinary residual factors remain explicit until ideal-multiplication transport. -/
def goodFiniteKernel (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (a b : PrimeIdeal → ℕ) (S : Finset (GoodPrimes bad)) (k : GoodIndex bad) : ℂ :=
  (∏ P : k.1,goodPrimeKernel χ₁ χ₂ ψ₁ ψ₂ a b P.val.val (k.2 P))*
    ∏ P ∈ S \ k.1,ordinaryLocalCoefficient χ₁ χ₂ a b P.val

/-- Existing `CorrectedIndex`, with no injectivity assumption on the extracted
ideal pair; different numerator choices can give the same pair. -/
def correctedFiniteKernel (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (a b : PrimeIdeal → ℕ)
    (S : Finset (GoodPrimes bad)) (k : CorrectedIndex bad allowed) : ℂ :=
  (∏ P : bad,exceptionalPrimeKernel χ₁ χ₂ ψ₁ ψ₂ a b P.val (k.2.1 P).val (k.1 P))*
    goodFiniteKernel χ₁ χ₂ ψ₁ ψ₂ bad a b S k.2.2

theorem correctedFiniteKernel_expansion (χ₁ χ₂ ψ₁ ψ₂ : Character) (bad : Finset PrimeIdeal)
    (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (a b : PrimeIdeal → ℕ)
    (S : Finset (GoodPrimes bad)) :
    (∏ P ∈ S,(ordinaryLocalCoefficient χ₁ χ₂ a b P.val+
      ∑ j : Fin 7,goodPrimeKernel χ₁ χ₂ ψ₁ ψ₂ a b P.val j)) *
      (∏ P : bad,∑ q : allowed P.val,∑ j : Fin 4,
        exceptionalPrimeKernel χ₁ χ₂ ψ₁ ψ₂ a b P.val q.val j) =
    ∑ q : BadIndex bad allowed, ∑ j : DeletionIndex bad,
      ∑ T ∈ S.powerset, ∑ k : T → Fin 7,
        correctedFiniteKernel χ₁ χ₂ ψ₁ ψ₂ bad allowed a b S (j,(q,⟨T,k⟩)) := by
  simp only [correctedFiniteKernel,goodFiniteKernel]
  rw [finite_good_expansion,finite_exceptional_expansion,mul_comm]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr (by ext; simp only [Finset.mem_univ]) ?_
  intro q _
  refine Finset.sum_congr (by ext; simp only [Finset.mem_univ]) ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro T _
  refine Finset.sum_congr (by ext; simp only [Finset.mem_univ]) ?_
  intro k _
  apply congrArg₂ (fun u v : ℂ => u*v)
  · exact Finset.prod_congr (by ext; simp only [Finset.mem_univ]) (fun _ _ => rfl)
  · apply congrArg₂ (fun u v : ℂ => u*v)
    · exact Finset.prod_congr (by ext; simp only [Finset.mem_univ]) (fun _ _ => rfl)
    · exact Finset.prod_congr (by ext; simp only [Finset.mem_sdiff]) (fun _ _ => rfl)


def goodPairSupport (bad : Finset PrimeIdeal) (I J : Ideal O) : Finset (GoodPrimes bad) :=
  (pairPrimeSupport I J).subtype (fun P => P ∉ bad)

lemma prod_goodPairSupport (bad : Finset PrimeIdeal) (I J : Ideal O) (f : PrimeIdeal → ℂ) :
    (∏ P ∈ goodPairSupport bad I J,f P.val) = ∏ P ∈ pairPrimeSupport I J \ bad,f P := by
  rw [goodPairSupport,Finset.prod_subtype_eq_prod_filter]
  congr 1
  ext P
  simp

theorem correctedPairEulerCoefficient_expansion (χ₁ χ₂ ψ₁ ψ₂ : Character)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (I J : Ideal O) :
    correctedPairEulerCoefficient χ₁ χ₂ ψ₁ ψ₂ bad allowed I J =
      ∑ q : BadIndex bad allowed, ∑ j : DeletionIndex bad,
        ∑ T ∈ (goodPairSupport bad I J).powerset, ∑ k : T → Fin 7,
          correctedFiniteKernel χ₁ χ₂ ψ₁ ψ₂ bad allowed
            (ProbePhysical.primeValuations I) (ProbePhysical.primeValuations J)
            (goodPairSupport bad I J) (j,(q,⟨T,k⟩)) := by
  rw [←correctedFiniteKernel_expansion]
  rw [prod_goodPairSupport bad I J (fun P =>
    ordinaryLocalCoefficient χ₁ χ₂ (ProbePhysical.primeValuations I) (ProbePhysical.primeValuations J) P+
      ∑ j : Fin 7,goodPrimeKernel χ₁ χ₂ ψ₁ ψ₂
        (ProbePhysical.primeValuations I) (ProbePhysical.primeValuations J) P j)]
  unfold correctedPairEulerCoefficient ordinaryLocalCoefficient goodPrimeKernel exceptionalPrimeKernel
  congr 1
  rw [←Finset.prod_coe_sort bad]
  apply Finset.prod_congr rfl
  intro P _
  exact (Finset.sum_coe_sort _ _).symm

#print axioms correctedPairEulerCoefficient_expansion
#print axioms correctedFiniteKernel_expansion
end
end QRH.Cycle092.SignedCenter
