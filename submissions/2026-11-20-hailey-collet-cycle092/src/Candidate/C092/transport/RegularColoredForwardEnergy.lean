/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Independent ordinary colors preserve the genuine H16 forward collision mass.
Only the original finite child norms occur as analytic inputs. -/
import Candidate.C092.transport.RegularColoredForwardFamily
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.NativeForwardEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower
open QRH.SilDensitySplit.CubeFree.FP
open KernelPhysicalScalars KernelCommonScalarMass KernelFamilyEnergy
open KernelRowPools KernelRowProfiles KernelMarkedRows KernelAssignmentReindex
open ReferenceForwardRows RestorationFamily RestorationInverseEnergy
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

/-- Multiplicative ordinary characters are contractions even at ramified
ideals; this is a bound, never an equality to a unit. -/
theorem color_norm_le_one (ω₁ ω₂ : Character) (d : Id × Id) :
    ‖color (idealCoeff ω₁) (idealCoeff ω₂) d‖ ≤ 1 := by
  rw [color,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one ω₁ d.1)).trans
    (idealCoeff_norm_le_one ω₂ d.2)

/-- Exact native scalar and exact H16 mass: ordinary colors are extracted
without replacing the collision coefficient or adding a label count. -/
theorem actual_subpower_energy (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ t ∈ F, Function.Injective t) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ t ∈ F, ∀ d ∈ D t, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ t ∈ F, ∀ d ∈ D t, pairSupport d.1 d.2 ⊆ primeValues S) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (ω₁ ω₂ : Id →*₀ ℂ),
      (∀ d : Id × Id, ‖color ω₁ ω₂ d‖ ≤ 1) →
      ∀ (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ G : (α → S) → (Id × Id) → Row → ℂ, ∀ E : ℝ, 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ t ∈ F, ∀ d ∈ D t, (∑ u ∈ rows, ρ u*‖G t d u‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u*‖∑ t ∈ F, ∑ d ∈ D t,
        scalar (χ u) S (ordinarySeriesFor false) (markedSeriesFor false)
          pool β P t d * color ω₁ ω₂ d * G t d u‖^2) ≤ C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := KernelFamilyEnergy.actual_subpower_energy (α:=α) false B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX S hS F hinj D hd hs Row rows ρ χ ω₁ ω₂ hω pool β P hP hp hβ G E hE hρ hG
  have hchild (t : α → S) (ht : t ∈ F) (d : Id × Id) (hdd : d ∈ D t) :
      (∑ u ∈ rows, ρ u*‖color ω₁ ω₂ d * G t d u‖^2) ≤ E := by
    apply (Finset.sum_le_sum ?_).trans (hG t ht d hdd)
    intro u hu
    apply mul_le_mul_of_nonneg_left _ (hρ u hu)
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hω d)
  have h := hbound X hX S hS F hinj D hd hs rows ρ χ pool β P hP hp hβ
    (fun t d u => color ω₁ ω₂ d * G t d u) E hE hρ hchild
  simpa only [mul_assoc] using h

/-- Finite weighted forward reduction of the actual two-color restricted
marked family. Children use the actual surviving slots and exact extracted
scales. The row weights remain arbitrary and nonnegative. -/
theorem finite_forward_energy (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ Q ∈ S, Supported Q.val ∧ (Q.val.absNorm : ℝ) ≤ X) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (ω₁ ω₂ : Id →*₀ ℂ),
      (∀ d : Id × Id, ‖color ω₁ ω₂ d‖ ≤ 1) →
      ∀ (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (I.absNorm : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ E : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ (T : Finset α) (frozen : T → S), Function.Injective frozen →
        ∀ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
          (∑ u ∈ rows, ρ u * ‖
            row (χ u) ω₁ ω₂
              (supportedRectangle S b (X₁/(d.1.absNorm : ℝ)) (X₂/(d.2.absNorm : ℝ)))
              (fun _ => 1) W₁ W₂ (X₁/(d.1.absNorm : ℝ)) (X₂/(d.2.absNorm : ℝ)) *
            remainingSum T (naturalCoefficients (χ u) S pool β P) frozen (fun _ => 1)‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u * ‖weightedSum (naturalCoefficients (χ u) S pool β P)
        (fun slot => row (χ u) ω₁ ω₂ (supportedRectangle S b X₁ X₂)
          (sourceValue false S slot) W₁ W₂ X₁ X₂)‖^2) ≤ C*X^ε*E := by
  choose CT hCT hbound using fun T : Finset α =>
    actual_subpower_energy (α:=T) B ε hB hε
  let C := 1 + ∑ T : Finset α, CT T
  have hC : 0 < C := by
    have hsum := Finset.sum_nonneg (fun T (_ : T ∈ (Finset.univ : Finset (Finset α))) => (hCT T).le)
    dsimp [C]
    linarith
  have hCTC (T : Finset α) : CT T ≤ C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CT)
      (fun T _ => (hCT T).le) (Finset.mem_univ T)
    dsimp [C]
    linarith
  refine ⟨(Fintype.card (Finset α) : ℝ)^2*C,by positivity,?_⟩
  intro X hX S hS Row rows ρ χ ω₁ ω₂ hω pool β P hP hp hβ W₁ W₂ b X₁ X₂ E hX₁ hX₂ hE hρ hchildren
  let D := divisorPool (supportedRectangle S b X₁ X₂)
  let G (T : Finset α) (frozen : T → S) (d : Id × Id) (u : Row) :=
    row (χ u) ω₁ ω₂
      (supportedRectangle S b (X₁/(d.1.absNorm : ℝ)) (X₂/(d.2.absNorm : ℝ)))
      (fun _ => 1) W₁ W₂ (X₁/(d.1.absNorm : ℝ)) (X₂/(d.2.absNorm : ℝ)) *
      remainingSum T (naturalCoefficients (χ u) S pool β P) frozen (fun _ => 1)
  let F (T : Finset α) (u : Row) := ∑ frozen ∈ frozenChoices T S, ∑ d ∈ D,
    scalar (χ u) S (ordinarySeriesFor false) (markedSeriesFor false)
      (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val) frozen d *
      color ω₁ ω₂ d * G T frozen d u
  have hF (T : Finset α) : (∑ u ∈ rows, ρ u*‖F T u‖^2) ≤ C*X^ε*E := by
    have hh := hbound T X hX S hS (frozenChoices T S)
      (fun t ht => (Finset.mem_filter.mp ht).2) (fun _ => D)
      (fun _ _ d hd => ⟨(divisor_supported hd).1,(divisor_supported hd).2.1⟩)
      (fun _ _ d hd => (divisor_supported hd).2.2)
      rows ρ χ ω₁ ω₂ hω (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val)
      (fun i => hP i.val) (fun i => hp i.val) (fun i => hβ i.val) (G T) E hE hρ
      (fun t ht d hd => hchildren T t (Finset.mem_filter.mp ht).2 d hd)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCTC T) (Real.rpow_nonneg (zero_le_one.trans hX) _)) hE)
  have hid (u : Row) : weightedSum (naturalCoefficients (χ u) S pool β P)
      (fun slot => row (χ u) ω₁ ω₂ (supportedRectangle S b X₁ X₂)
        (sourceValue false S slot) W₁ W₂ X₁ X₂) = ∑ T : Finset α, F T u := by
    rw [natural_rectangle_expansion S (χ u) ω₁ ω₂ pool β P W₁ W₂ b X₁ X₂ hX₁ hX₂]
    apply Finset.sum_congr rfl
    intro T hT
    simp only [F,frozenChoices,Finset.sum_filter]
    apply Finset.sum_congr (by ext; simp)
    intro frozen hfrozen
    split_ifs
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [childValue,Bool.false_eq_true,ite_false]
      rw [remaining_constant]
    · rfl
  have hh := KernelCollisionEnergy.weighted_physical_energy rows ρ F F (fun _ => 1)
    (C*X^ε*E) hρ (fun _ => zero_le_one) (by intros; simp) hF
  calc
    _ = ∑ u ∈ rows, ρ u*‖∑ T : Finset α, F T u‖^2 := by simp_rw [hid]
    _ ≤ _ := by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,mul_assoc] using hh

#print axioms color_norm_le_one
#print axioms actual_subpower_energy
#print axioms finite_forward_energy
end
end QRH.Cycle092.RegularColoredForward
