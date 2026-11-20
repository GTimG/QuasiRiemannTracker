/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Actual signed independent-column inverse restoration in one physical norm. -/
import Candidate.C092.transport.ColoredRootRestoreSigned
import Candidate.C092.transport.ColoredRootRestoreScalar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP
open KernelPhysicalScalars KernelCommonScalarMass KernelFamilyEnergy
open KernelRowPools KernelRowProfiles KernelMarkedRows KernelAssignmentReindex
open RestorationFamily RestorationInverseEnergy QRH.Cycle092.RegularColoredForward
local notation "Id" => Ideal HeckeFamily.O
variable {α:Type*} [Fintype α]

theorem signed_inverse_energy (B ε:ℝ) (hB:0≤B) (hε:0<ε) :
    ∃ C:ℝ,0<C ∧ ∀ X:ℝ,1≤X → ∀ S:Finset PrimeIdeal,
      (∀ Q∈S,Supported Q.val ∧ (Q.val.absNorm:ℝ)≤X) →
      ∀ {Row:Type*} (rows:Finset Row) (ρ:Row→ℝ) (χ:Row→Character)
        (ω₁ ω₂:Id→*₀ℂ),(∀ d:Id×Id,‖color ω₁ ω₂ d‖≤1) →
      ∀ (pool:α→Finset Id) (β:α→Id→ℂ) (P:α→ℝ),
      (∀ i,0<P i) → (∀ i I,I∈pool i → Supported I ∧ (I.absNorm:ℝ)≤2*P i) →
      (∀ i I,I∈pool i → ‖β i I‖≤B) →
      ∀ (W₁ W₂:ℝ→ℂ) (b M₁ M₂ X₁ X₂ Y₁ Y₂:ℝ) (cX cY:ℂ) (E:ℝ),
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → 0≤E → (∀ u∈rows,0≤ρ u) →
      (∀ (T:Finset α) (ti:T→S),Function.Injective ti →
        ∀ d∈divisorPool (supportedRectangle S b M₁ M₂),
        (∑ u∈rows,ρ u*‖signedRow false S (χ u) ω₁ ω₂
          (fun i:{i // i∉T}=>pool i.val) (crossBeta T S ti β) (fun i=>P i.val)
          (residualPool (supportedRectangle S b M₁ M₂) d) W₁ W₂
          (X₁/d.1.absNorm) (X₂/d.2.absNorm) (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) cX cY‖^2)≤E) →
      (∑ u∈rows,ρ u*‖signedRow true S (χ u) ω₁ ω₂ pool β P
        (supportedRectangle S b M₁ M₂) W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY‖^2)≤C*X^ε*E := by
  choose CT hCT hbound using fun T : Finset α =>
    colored_subpower_energy (α:=T) true B ε hB hε
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
  intro X hX S hS Row rows ρ χ ω₁ ω₂ hω pool β P hP hp hβ W₁ W₂ b M₁ M₂ X₁ X₂ Y₁ Y₂ cX cY E hX₁ hX₂ hY₁ hY₂ hE hρ hchildren
  let D := divisorPool (supportedRectangle S b M₁ M₂)
  let G (T:Finset α) (frozen:T→S) (d:Id×Id) (u:Row) :=
    signedRow false S (χ u) ω₁ ω₂ (fun i:{i // i∉T}=>pool i.val)
      (crossBeta T S frozen β) (fun i=>P i.val)
      (residualPool (supportedRectangle S b M₁ M₂) d) W₁ W₂
      (X₁/d.1.absNorm) (X₂/d.2.absNorm) (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) cX cY
  let F (T : Finset α) (u : Row) := ∑ frozen ∈ frozenChoices T S, ∑ d ∈ D,
    scalar (χ u) S (ordinarySeriesFor true) (markedSeriesFor true)
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
  have hid (u:Row) : signedRow true S (χ u) ω₁ ω₂ pool β P
      (supportedRectangle S b M₁ M₂) W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY = ∑ T:Finset α,F T u :=
    signed_inverse_expansion S (χ u) ω₁ ω₂ pool β P _
      (fun _ h=>supportedRectangle_nonzero h) (fun _ h=>(Finset.mem_filter.mp h).2)
      W₁ W₂ X₁ X₂ Y₁ Y₂ cX cY hX₁ hX₂ hY₁ hY₂
  have hh := KernelCollisionEnergy.weighted_physical_energy rows ρ F F (fun _ => 1)
    (C*X^ε*E) hρ (fun _ => zero_le_one) (by intros; simp) hF
  calc
    _ = ∑ u ∈ rows, ρ u*‖∑ T : Finset α, F T u‖^2 := by simp_rw [hid]
    _ ≤ _ := by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,mul_assoc] using hh


#print axioms signed_inverse_energy
end
end QRH.Cycle092.ColoredRootRestore
