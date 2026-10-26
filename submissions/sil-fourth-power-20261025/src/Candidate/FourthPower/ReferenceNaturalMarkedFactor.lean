/- Copyright (c) 2026 Sil. Apache-2.0.
Exact grouping of the original annular prime slots, including the live
injectivity and frozen-prime holes of the actual restoration expansion.
-/
import Candidate.FourthPower.ReferenceJointFactor
import Candidate.FourthPower.KernelMarkedRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.ReferenceNaturalMarkedFactor
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferenceFactors ReferenceJointFactor KernelNaturalSlots
open KernelMarkedRows KernelAssignmentReindex
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

def idealTuple (S : Finset PrimeIdeal) (s : α → S) : α → Id := fun i => (s i).val.val

theorem idealTuple_injective (S : Finset PrimeIdeal) : Function.Injective (idealTuple (α:=α) S) := by
  intro s t h
  funext i
  apply Subtype.ext
  apply Subtype.ext
  exact congrFun h i

def liveAssignments (S : Finset PrimeIdeal) (pool : α → Finset Id)
    (Accept : (α → S) → Prop) : Finset (α → S) :=
  Finset.univ.filter (fun s => Accept s ∧ ∀ i, (s i).val.val ∈ pool i)

theorem actual_tuple_identity (S : Finset PrimeIdeal) (pool : α → Finset Id)
    (β : α → Id → ℂ) (P : α → ℝ) (Accept : (α → S) → Prop) (χ : Character) :
    (∑ v ∈ (liveAssignments S pool Accept).image (idealTuple S),
      ∏ i, ((Real.sqrt (P i) : ℂ)⁻¹*β i (v i))*idealCoeff χ (v i)) =
    ∑ s : α → S, if Accept s then ∏ i, slotTerm χ (pool i) (β i) (P i) (s i).val.val else 0 := by
  rw [Finset.sum_image (fun s _ t _ h => idealTuple_injective S h)]
  unfold liveAssignments
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases ha : Accept s
  · by_cases hp : ∀ i, (s i).val.val ∈ pool i
    · rw [ite_eq_left ⟨ha,hp⟩,ite_eq_left ha]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [idealTuple,slotTerm,hp i,ite_true]
      ring
    · simp only [ha,true_and,hp,ite_false,ite_true]
      obtain ⟨i,hi⟩ := not_forall.mp hp
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [slotTerm,hi])
  · simp [ha]

/-- The grouped factor is constructed before the physical character is
chosen. Its length is the original live product, with no rounding to one. -/
theorem actual_tuple_factor (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset PrimeIdeal) (pool : α → Finset Id)
      (β : α → Id → ℂ) (P : α → ℝ) (B : ℝ),
      0 ≤ B → (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ Accept : (α → S) → Prop,
      ∃ F : Factor, F.length = ∏ i, 2*P i ∧
        F.amplitude = C*(max 1 (∏ i, 2*P i))^δ*(Real.sqrt 2*B)^Fintype.card α ∧
        ∀ χ : Character, F.value χ =
          ∑ s : α → S, if Accept s then ∏ i, slotTerm χ (pool i) (β i) (P i) (s i).val.val else 0 := by
  obtain ⟨C,hC,hjoint⟩ := joint_factor (α:=α) δ hδ
  refine ⟨C,hC,?_⟩
  intro S pool β P B hB hP hp hβ Accept
  let H (i : α) := Factor.marked (pool i) (β i) (P i) B (hP i) hB
    (fun I hI => ⟨(hp i I hI).1.1,(hp i I hI).2⟩) (hβ i)
  let V := (liveAssignments S pool Accept).image (idealTuple S)
  have hV (v) (hv : v ∈ V) (i : α) : Supported (v i) ∧ v i ∈ (H i).pool := by
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
    have hmem := (Finset.mem_filter.mp hs).2.2 i
    exact ⟨(hp i _ hmem).1,hmem⟩
  obtain ⟨F,hFl,hFa,hvalue⟩ := hjoint H V (fun _ => 1) hV (fun _ _ => by simp)
  refine ⟨F,?_,?_,?_⟩
  · simpa only [H,Factor.marked] using hFl
  · simpa only [H,Factor.marked,Finset.prod_const,Finset.card_univ] using hFa
  · intro χ
    rw [hvalue]
    simpa only [H,Factor.marked,V,one_mul] using actual_tuple_identity S pool β P Accept χ

/-- This is the literal residual marked polynomial used by
KernelMarkedRows.natural_rectangle_expansion, with all cross-holes retained. -/
theorem remaining_factor (T : Finset α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset PrimeIdeal) (pool : α → Finset Id)
      (β : α → Id → ℂ) (P : α → ℝ) (B : ℝ),
      0 ≤ B → (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ t : T → S, ∃ F : Factor,
        F.length = ∏ i : {i // i ∉ T}, 2*P i.val ∧
        F.amplitude = C*(max 1 (∏ i : {i // i ∉ T}, 2*P i.val))^δ*
          (Real.sqrt 2*B)^Fintype.card {i // i ∉ T} ∧
        ∀ χ : Character,
          remainingSum T (naturalCoefficients χ S pool β P) t (fun _ => 1) = F.value χ := by
  obtain ⟨C,hC,hfactor⟩ := actual_tuple_factor (α:={i // i ∉ T}) δ hδ
  refine ⟨C,hC,?_⟩
  intro S pool β P B hB hP hp hβ t
  obtain ⟨F,hlen,hamp,hvalue⟩ := hfactor S (fun i => pool i.val) (fun i => β i.val)
    (fun i => P i.val) B hB (fun i => hP i.val) (fun i => hp i.val) (fun i => hβ i.val)
    (fun s => Function.Injective s ∧ ∀ i j, t i ≠ s j)
  refine ⟨F,hlen,hamp,?_⟩
  intro χ
  symm
  apply (hvalue χ).trans
  unfold remainingSum naturalCoefficients
  apply Finset.sum_congr (by ext; simp)
  intro s hs
  split_ifs <;> simp only [one_mul]

end
end Candidate.FourthPower.ReferenceNaturalMarkedFactor
