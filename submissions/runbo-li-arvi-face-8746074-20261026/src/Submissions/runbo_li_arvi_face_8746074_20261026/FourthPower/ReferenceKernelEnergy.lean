/- Copyright (c) 2026 Sil. Apache-2.0.
The actual forward extraction scalars applied to original Hecke products.
Every child-energy input is discharged by the selected analytic reference.
Length and profile bounds are explicit; fixed-hole restoration is separate.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.ReferenceSelectedEnergy
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.KernelReflectedEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.ReferenceKernelEnergy
noncomputable section
open scoped Classical BigOperators ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CanonicalQuadraticSieve CanonicalRowCompletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferenceFactors ReferenceHeckeProducts ReferenceExtractionGeometry
open KernelAllocationIdentity KernelPhysicalScalars
open CenteredMomentScaleSupremum
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {Frozen Live : Type*} [Fintype Frozen] [Fintype Live]

theorem forward_product_reference (ε L K a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 0 ≤ Bf) :
    ∃ n : ℕ, ∀ Wlong : ℝ → ℂ,
      Function.support Wlong ⊆ Icc a b → ContDiff ℝ ∞ Wlong →
      ∃ C : ℝ, 0 < C ∧ ∀ (Z R v y ratio : ℝ),
      1 ≤ Z → 0 ≤ R → 0 ≤ v → 0 ≤ y → 0 ≤ ratio →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 →
      ∀ (η : Character) (m D₀ : O) (rows : Finset O) (χ : rows → Character),
      (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D₀ I*idealRowHom x.val I) →
      (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ i, (χ i).residue ≠ 1) →
      ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ Z^K) →
      ∀ F : Finset (Frozen → S), (∀ t ∈ F, Function.Injective t) →
      ∀ D : (Frozen → S) → Finset (Id × Id),
      (∀ t ∈ F, ∀ d ∈ D t, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ t ∈ F, ∀ d ∈ D t, pairSupport d.1 d.2 ⊆ primeValues S) →
      ∀ (pool : Frozen → Finset Id) (β : Frozen → Id → ℂ) (P : Frozen → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ Bf) →
      ∀ (U Height A : ℝ) (Wshort : ℝ → ℂ) (c d B : ℝ),
      1 ≤ U → U ≤ Z^K → 0 ≤ Height → 0 ≤ A →
      (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ U) →
      0 ≤ d → 0 ≤ B → Function.support Wshort ⊆ Icc c d → ContDiff ℝ ∞ Wshort →
      (∀ (j : Fin 2) (x : ℝ), ‖scaleTest Wshort j x‖ ≤ B) →
      ∀ (X Xshort t omega : (Frozen → S) → (Id × Id) → ℝ)
        (H : (Frozen → S) → (Id × Id) → Live → Factor),
      (∀ j ∈ F, ∀ e ∈ D j, 0 < X j e ∧ 0 < Xshort j e) →
      (∀ j ∈ F, ∀ e ∈ D j, ‖t j e‖ ≤ Height) →
      (∀ j ∈ F, ∀ e ∈ D j, Real.sqrt d*B*(∏ i, (H j e i).amplitude) ≤ A) →
      (∀ j ∈ F, ∀ e ∈ D j, d*Xshort j e*(∏ i, (H j e i).length) ≤ Z^L) →
      (∀ j ∈ F, ∀ e ∈ D j,
        branchCap b (Z^(xi/2)) (X j e) U*(d*Xshort j e)*(∏ i, (H j e i).length) ≤ Z^v) →
      (∀ j ∈ F, ∀ e ∈ D j,
        branchCap b (Z^(xi/2)) (X j e) U*(d*Xshort j e)*(∏ i, (H j e i).length) ≤
          Z^y*ratio*((Ideal.absNorm e.2 : ℝ)/((Ideal.absNorm e.1 : ℝ)*frozenNorm S j))) →
      (∑ i : rows, ‖∑ j ∈ F, ∑ e ∈ D j,
        scalar (χ i) S (ordinarySeriesFor false) (markedSeriesFor false) pool β P j e *
          (polynomial (χ i) false Wlong (X j e) 0 (2*Real.pi*t j e)*
            polynomial (χ i) false Wshort (Xshort j e) 0 (2*Real.pi*omega j e)*
              ∏ k, (H j e k).value (χ i))‖^2) ≤
        C*(1+Height)^(2*n)*Z^(R+ε)*A^2*(3+ratio^(1/3 : ℝ)) := by
  obtain ⟨n,hn⟩ := ReferenceSelectedEnergy.selected_reference (α:=Live) (ε/2) L K a b xi
    (half_pos hε) hL hK ha hb hxi
  obtain ⟨Cm,hCm,hm⟩ := KernelReflectedEnergy.actual_reflected_subpower (α:=Frozen) Bf
    (ε/(2*K)) hBf (div_pos hε (by positivity))
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨Cr,hCr,hr⟩ := hn Wlong hs hW
  refine ⟨Cm*Cr,mul_pos hCm hCr,?_⟩
  intro Z R v y ratio hZ hR hv0 hy0 hratio hcap hv hy η m D₀ rows χ hon hoff hrows hnonprincipal
  intro S hS F hinj D hd hsD pool β P hP hp hβ U Height A Wshort c d B
  intro hU hUcap hHeight hA hmod hd0 hB hshort hshortsmooth htest
  intro X Xshort t omega H hX ht hamp hvolume hmax href
  let G (j : Frozen → S) (e : Id × Id) (i : rows) :=
    polynomial (χ i) false Wlong (X j e) 0 (2*Real.pi*t j e)*
      polynomial (χ i) false Wshort (Xshort j e) 0 (2*Real.pi*omega j e)*
        ∏ k, (H j e k).value (χ i)
  let E := Cr*(1+Height)^(2*n)*Z^(R+ε/2)*A^2*(3+ratio^(1/3 : ℝ))
  have hZp := zero_lt_one.trans_le hZ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hchild (j) (hj : j ∈ F) (e) (he : e ∈ D j) :
      (∑ i : rows, ‖G j e i‖^2) ≤
        E*(3+((Ideal.absNorm e.2 : ℝ)/((Ideal.absNorm e.1 : ℝ)*frozenNorm S j))^(1/3 : ℝ)) := by
    let r := (Ideal.absNorm e.2 : ℝ)/((Ideal.absNorm e.1 : ℝ)*frozenNorm S j)
    have hr0 : 0 ≤ r := by
      have := frozenNorm_pos S j
      dsimp [r]
      positivity
    have hcost : 3+(ratio*r)^(1/3 : ℝ) ≤ (3+ratio^(1/3 : ℝ))*(3+r^(1/3 : ℝ)) := by
      rw [Real.mul_rpow hratio hr0]
      have ha := Real.rpow_nonneg hratio (1/3 : ℝ)
      have hb := Real.rpow_nonneg hr0 (1/3 : ℝ)
      nlinarith
    have hh := hr Z R v y (ratio*r) hZ hR hv0 hy0 (mul_nonneg hratio hr0) hcap hv hy η m D₀ rows χ hon hoff
      hrows hnonprincipal U (X j e) (Xshort j e) Height (t j e) (omega j e)
      Wshort c d B (H j e) hU hUcap (hX j hj e he).1 (hX j hj e he).2
      hHeight (ht j hj e he) hmod hd0 hB hshort hshortsmooth htest
      (hvolume j hj e he) (hmax j hj e he) (by simpa only [r,mul_assoc] using href j hj e he)
    have ha0 : 0 ≤ Real.sqrt d*B*∏ k, (H j e k).amplitude :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB)
        (Finset.prod_nonneg (fun k _ => (H j e k).amplitude_nonneg))
    apply hh.trans
    calc
      _ ≤ Cr*(1+Height)^(2*n)*Z^(R+ε/2)*
          (3+(ratio*r)^(1/3 : ℝ))*A^2 := by
        gcongr
        exact hamp j hj e he
      _ ≤ Cr*(1+Height)^(2*n)*Z^(R+ε/2)*
          ((3+ratio^(1/3 : ℝ))*(3+r^(1/3 : ℝ)))*A^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost (by positivity)) (sq_nonneg A)
      _ = _ := by dsimp [E,r]; ring
  have hh := hm (Z^K) (Real.one_le_rpow hZ hK.le) S hS F hinj D hd hsD
    (Finset.univ : Finset rows) (fun _ => 1) χ pool β P hP hp hβ G E hE
    (fun _ _ => zero_le_one) (by
      intro j hj e he
      simpa only [one_mul] using hchild j hj e he)
  simp only [one_mul] at hh
  have hpow : (Z^K)^(ε/(2*K)) = Z^(ε/2) := by
    rw [← Real.rpow_mul hZp.le]
    congr 1
    field_simp
  apply hh.trans_eq
  rw [hpow]
  dsimp [E]
  calc
    _ = (Cm*Cr)*(1+Height)^(2*n)*(Z^(ε/2)*Z^(R+ε/2))*A^2*(3+ratio^(1/3 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZp]
      congr 3
      congr 1
      ring

end
end Candidate.FourthPower.ReferenceKernelEnergy
