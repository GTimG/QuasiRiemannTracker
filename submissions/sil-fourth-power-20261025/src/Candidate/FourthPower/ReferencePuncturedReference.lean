/- Copyright (c) 2026 Sil. Apache-2.0.
Unconditional reference with common ordinary punctures on polynomial support.
The conductor and profiles stay unchanged. All residual moment inputs are
discharged by the ratio-uniform fifth-free reference, not assumed.
-/
import Candidate.FourthPower.ReferenceRestrictedReference
import Candidate.FourthPower.KernelPunctureFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.ReferencePuncturedReference
noncomputable section
open scoped Classical BigOperators ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CanonicalQuadraticSieve CanonicalRowCompletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferenceFactors ReferenceHeckeProducts ReferencePrimeEnclosure
open KernelAssignmentReindex KernelMarkedRows KernelLabelledSlots KernelRowExpansion
open KernelRowProfiles KernelRowPools KernelPunctureRows
open CenteredMomentScaleSupremum
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

theorem punctured_reference (ε L K a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
    ∃ n : ℕ, ∀ Wlong : ℝ → ℂ,
      Function.support Wlong ⊆ Icc a b → ContDiff ℝ ∞ Wlong →
      ∃ C : ℝ, 0 < C ∧ ∀ (Z R v y : ℝ),
      1 ≤ Z → 0 ≤ R → 0 ≤ v → 0 ≤ y → R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 →
      ∀ (η : Character) (m D₀ : O) (rows : Finset O) (χ : rows → Character),
      (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D₀ I*idealRowHom x.val I) →
      (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ i, (χ i).residue ≠ 1) →
      ∀ (U X₁ X₂ Height t₁ t₂ : ℝ) (Wshort : ℝ → ℂ) (B : ℝ),
      1 ≤ U → U ≤ Z^K → 0 < X₁ → 0 < X₂ → 0 ≤ Height → ‖t₂‖ ≤ Height →
      (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ U) →
      0 ≤ B → Function.support Wshort ⊆ Icc a b → ContDiff ℝ ∞ Wshort →
      (∀ (j : Fin 2) (x : ℝ), ‖scaleTest Wshort j x‖ ≤ B) →
      ∀ (S H : Finset PrimeIdeal) (F : Id), F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^K →
      (∀ Q ∈ H, Q.val ∣ F) →
      (∀ Q ∈ S, Supported Q.val ∧ (Ideal.absNorm Q.val : ℝ) ≤ Z^K) →
      (∀ I, Supported I →
        ((Ideal.absNorm I : ℝ) ≤ b*X₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues S) →
      ∀ (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ Bf) →
      (∀ i Q, Q ∈ H → β i Q.val=0) →
      (∏ i, 2*P i) ≤ Z^L → b*X₁*(∏ i, 2*P i) ≤ Z^L →
      (b+4)*Z^(xi/2)*b*X₁*(∏ i, 2*P i)*Real.sqrt U ≤ Z^v →
      (b+4)*Z^(xi/2)*b*(X₁*(∏ i, 2*P i)*U/X₂) ≤ Z^y →
      (∑ i : rows, ‖weightedSum (naturalCoefficients (χ i) S pool β P)
        (fun slot => normalizedRow (χ i) (supportedRectangle S b X₁ X₂)
          (restrictedValue S (augmented S H (marked S slot)))
          (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) X₁ X₂)‖^2) ≤
        C*(1+Height)^(2*n)*Z^(R+ε)*B^2 := by
  obtain ⟨n,hn⟩ := ReferenceRestrictedReference.restricted_reference (α:=α)
    (ε/2) L K a b xi Bf (half_pos hε) hL hK ha hb hxi hBf
  obtain ⟨Cm,hCm,hm⟩ := KernelPunctureFamily.energy K (ε/2) hK.le (half_pos hε)
  refine ⟨n,?_⟩
  intro Wlong hlong hlongsmooth
  obtain ⟨Cr,hCr,hr⟩ := hn Wlong hlong hlongsmooth
  refine ⟨Cm*Cr,mul_pos hCm hCr,?_⟩
  intro Z R v y hZ hR hv0 hy0 hcap hv hy η m D₀ rows χ hon hoff hrows hnonprincipal
  intro U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hX₁ hX₂ hHeight ht₂ hmod hB hshort hshortsmooth htest
  intro S H F hF hFcap hH hS henclose pool β P hP hp hβ hβH hVcap hvolume hmax href
  let V := ∏ i, 2*P i
  have hV : 0 ≤ V := Finset.prod_nonneg (fun i _ => by have := hP i; positivity)
  let D := divisorPool (supportedRectangle S b X₁ X₂)
  let G (d : IdealPair) (i : rows) :=
    weightedSum (naturalCoefficients (χ i) S pool β P)
      (fun slot => normalizedRow (χ i)
        (supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
        (sourceValue false S slot) (phaseProfile Wshort t₁) (phaseProfile Wlong t₂)
        (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
  let E := Cr*(1+Height)^(2*n)*Z^(R+ε/2)*B^2
  have hZp := zero_lt_one.trans_le hZ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hchild (d : IdealPair) (hd : d ∈ D) :
      (∑ i : rows, ‖G d i‖^2) ≤ E*(3+((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/3 : ℝ)) := by
    have hds := divisor_supported hd
    have h₁ := shortened_positive_le hX₁ hds.1
    have h₂ := shortened_positive_le hX₂ hds.2.1
    have hnorm₁ : (0 : ℝ) < Ideal.absNorm d.1 := zero_lt_one.trans_le (ideal_norm_one_le hds.1)
    have hnorm₂ : (0 : ℝ) < Ideal.absNorm d.2 := zero_lt_one.trans_le (ideal_norm_one_le hds.2.1)
    have hvol : b*(X₁/Ideal.absNorm d.1)*V ≤ Z^L := by
      apply le_trans _ hvolume
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁.2 hb) hV
    have hmax' : (b+4)*Z^(xi/2)*b*(X₁/Ideal.absNorm d.1)*V*Real.sqrt U ≤ Z^v := by
      apply le_trans _ hmax
      gcongr
      exact h₁.2
    have href' : (b+4)*Z^(xi/2)*b*((X₁/Ideal.absNorm d.1)*V*U/(X₂/Ideal.absNorm d.2)) ≤
        Z^y*((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ)) := by
      calc
        _ = ((b+4)*Z^(xi/2)*b*(X₁*V*U/X₂))*
            ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ)) := by
          field_simp
          <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_right href (by positivity)
    have hh := hr Z R v y ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))
      hZ hR hv0 hy0 (by positivity) hcap hv hy η m D₀ rows χ hon hoff hrows hnonprincipal
      U (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) Height t₁ t₂ Wshort B
      hU hUcap h₁.1 h₂.1 hHeight ht₂ hmod hB hshort hshortsmooth htest S hS (by
        intro I hI hlen
        apply henclose I hI
        rcases hlen with hh | hh
        · exact Or.inl (hh.trans (mul_le_mul_of_nonneg_left h₁.2 hb))
        · exact Or.inr (hh.trans (mul_le_mul_of_nonneg_left h₂.2 hb)))
      pool β P hP hp hβ hVcap hvol hmax' href'
    exact hh
  have hh := hm Z hZ F hF hFcap S H (fun Q hQ => (hS Q hQ).1) hH D
    (fun d hd => ⟨(divisor_supported hd).1,(divisor_supported hd).2.1⟩)
    (fun d hd => (divisor_supported hd).2.2) (Finset.univ : Finset rows) (fun _ => 1) χ G E hE
    (fun _ _ => zero_le_one) (fun d hd => by simpa only [one_mul] using hchild d hd)
  simp only [one_mul] at hh
  have hid (i : rows) := KernelPunctureFamily.family_expansion S H
    (naturalCoefficients (χ i) S pool β P) (by
      intro j Q hQ
      simp [naturalCoefficients,KernelNaturalSlots.slotTerm,hβH j Q.val hQ])
    (χ i) (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) b X₁ X₂ hX₁ hX₂
  simp_rw [hid]
  change (∑ i : rows, ‖∑ d ∈ D,
    extractedScalar (χ i) (fun e => (KernelAllocationIdentity.kernelOn S
      (fun Q => KernelPunctureMass.atPrime H Q.val) e.1 e.2 : ℂ)) d*G d i‖^2) ≤ _
  apply hh.trans_eq
  dsimp [E]
  calc
    _ = (Cm*Cr)*(1+Height)^(2*n)*(Z^(ε/2)*Z^(R+ε/2))*B^2 := by ring
    _ = _ := by
      rw [← Real.rpow_add hZp]
      congr 2
      congr 1
      ring

end
end Candidate.FourthPower.ReferencePuncturedReference
