/- Copyright (c) 2026 Sil. Apache-2.0.
Homogeneous original reference energy on actual nonprincipal physical rows.
The retained part and discarded tail use a common finite ordinary-profile
control, chosen before the profile. All geometric gates and the post-sieve
factor are those of ReferenceOriginalEnergy.original_reference.
-/
import Candidate.SilPrior.FourthPower.ReferenceUniformRetainedEnergy
import Candidate.SilPrior.FourthPower.ReferenceUniformApproximation
import Candidate.SilPrior.FourthPower.ReferenceTailEnergy

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReferenceUniformOriginalEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CanonicalRowCompletion CanonicalQuadraticSieve
open ReferenceFactors ReferenceHeckeProducts ReferenceCrudeFactors ReferenceTailEnergy
open CenteredMomentNaturalPrimitive CenteredMomentOriginalReflectionApproximation
open CenteredMomentScaleSupremum CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]

theorem original_reference (ε L K Ltail a b xi : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a) (hxi : 0 < xi) :
    ∃ n : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ S ∧
      ∀ Wlong : 𝓢(ℝ,ℂ), Function.support (Wlong : ℝ → ℂ) ⊆ Icc a b →
      ∀ (Z R v y N T : ℝ),
      1 ≤ Z → 0 ≤ R → 1 ≤ N → 0 ≤ T →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 → N ≤ Z^v → N ≤ Z^y*T →
      ∀ (η : Character) (m D : O) (rows : Finset O) (χ : rows → Character),
      (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D I*idealRowHom x.val I) →
      (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ i, (χ i).residue ≠ 1) → (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ Z^K) →
      ∀ (U Y Xshort Height omega : ℝ) (X t : rows → ℝ) (Wshort : ℝ → ℂ)
        (c d B : ℝ) (F : α → Factor),
      1 ≤ Y → 0 < Xshort → 0 ≤ Height → (∀ i, 0 < X i) →
      (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ U) →
      (∀ i, 4*Z^(xi/2)*(U/X i) ≤ Y) →
      (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ Z^Ltail*X i) →
      (∀ i, ‖t i‖ ≤ Height) →
      0 ≤ d → 0 ≤ B → Function.support Wshort ⊆ Icc c d → ContDiff ℝ ∞ Wshort →
      (∀ (j : Fin 2) (x : ℝ), ‖scaleTest Wshort j x‖ ≤ B) →
      Y*(d*Xshort)*(∏ i, (F i).length) ≤ N →
      (∑ i : rows, ‖polynomial (χ i) false Wlong (X i) 0 (2*Real.pi*t i)*
        polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*
          ∏ j, (F j).value (χ i)‖^2) ≤
        C*(sourceControl S Wlong)^2*(1+Height)^(2*n)*(1+2*Real.log Y)*
          Z^(R+ε)*(3+T^(1/3 : ℝ))*(Real.sqrt d*B*∏ j, (F j).amplitude)^2 := by
  obtain ⟨nr,Sr,Cr,hCr,hSr0,hretained⟩ :=
    ReferenceUniformRetainedEnergy.retained_reference (α:=α) ε L K a b hε hL hK ha
  obtain ⟨nt,St,Ct,hCt,hSt0,happrox⟩ :=
    ReferenceUniformApproximation.original_approximation a b xi (L+1) K Ltail ha hxi hK
  let S := Sr ∪ St
  let κ : ℝ := 128^(Fintype.card α+1)
  let Ce : ℝ := 128*(Ct*κ)^2
  have hCe : 0 ≤ Ce := by dsimp only [Ce]; positivity
  have hS0 : (0,0) ∈ S := Finset.mem_union_left _ hSr0
  refine ⟨max nr nt,S,2*(Cr+Ce),by positivity,hS0,?_⟩
  intro Wlong hs Z R v y N T hZ hR hN hT hcap hv hy hmax href η m D rows χ hon hoff hr hnonprincipal hmod
  intro U Y Xshort Height omega X t Wshort c d B F hY hXshort hHeight hX hU hYcap hXcap ht
  intro hd hB hshort hshortsmooth htest hlen
  let control := sourceControl S Wlong
  have hcontrol : 0 ≤ control := sourceControl_nonneg S Wlong
  have hSr : sourceControl Sr Wlong ≤ control := by
    exact Seminorm.le_def.mp
      (Finset.sup_mono (Finset.subset_union_left : Sr ⊆ Sr ∪ St)) Wlong
  have hSt : sourceControl St Wlong ≤ control := by
    exact Seminorm.le_def.mp
      (Finset.sup_mono (Finset.subset_union_right : St ⊆ Sr ∪ St)) Wlong
  choose ψ G hprim hne hG hc he using fun i => happrox Wlong hs (χ i) (hnonprincipal i)
  let amp := Real.sqrt d*B*∏ j, (F j).amplitude
  let P (i : rows) := polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*∏ j, (F j).value (χ i)
  let retained (i : rows) := retainedOriginal (χ i) (ψ i) Wlong (X i) (Z^(xi/2)) (t i)
  let err (i : rows) := polynomial (χ i) false Wlong (X i) 0 (2*Real.pi*t i)-G i*retained i
  let E := control^2*(1+Height)^(2*max nr nt)*(1+2*Real.log Y)*Z^(R+ε)*(3+T^(1/3 : ℝ))*amp^2
  have hamp : 0 ≤ amp := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB)
      (Finset.prod_nonneg (fun i _ => (F i).amplitude_nonneg))
  have hvol : 0 ≤ d*Xshort*∏ i, (F i).length :=
    mul_nonneg (mul_nonneg hd hXshort.le) (Finset.prod_nonneg (fun i _ => (F i).length_nonneg))
  have hvolume : d*Xshort*(∏ i, (F i).length) ≤ Z^L := by
    have hh : d*Xshort*(∏ i, (F i).length) ≤ N :=
      (le_mul_of_one_le_left hvol hY).trans (by simpa only [mul_assoc] using hlen)
    exact hh.trans (hmax.trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)))
  have hP (i : rows) : ‖P i‖ ≤ κ*Z^L*amp := by
    have hh := smooth_product_norm (χ i) Wshort d B Xshort omega hd hB hXshort
      (fun x => by simpa only [scaleTest,ite_true] using htest 0 x)
      (fun x hx => (hshort hx).2) F
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvolume (by positivity)) hamp)
  have herr (i : rows) : ‖err i‖ ≤ (Ct*control)*(1+Height)^nt*Z^(-(L+1)) := by
    apply (he i (X i) (t i) Z (hX i) hZ (hmod i) (hXcap i)).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hSt hCt.le)
      (pow_le_pow_left₀ (by positivity) (by linarith [ht i]) nt)
      (by positivity) (mul_nonneg hCt.le hcontrol)
  have heSum := powered_error_energy rows err P Z R ε L (Ct*control) κ Height amp nt
    hZ hR hε.le (mul_nonneg hCt.le hcontrol) (by positivity) hHeight hamp hr herr hP
  have hbox : 1 ≤ 1+2*Real.log Y := by linarith [Real.log_nonneg hY]
  have hterm : 1 ≤ 3+T^(1/3 : ℝ) := by have := Real.rpow_nonneg hT (1/3 : ℝ); linarith
  have hnrpow : (1+Height)^(2*nr) ≤ (1+Height)^(2*max nr nt) :=
    pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left 2 (Nat.le_max_left nr nt))
  have hntpow : (1+Height)^(2*nt) ≤ (1+Height)^(2*max nr nt) :=
    pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left 2 (Nat.le_max_right nr nt))
  have hePaid : (∑ i : rows, ‖err i*P i‖^2) ≤ Ce*E := by
    apply heSum.trans
    calc
      _ = Ce*control^2*(1+Height)^(2*nt)*Z^(R+ε)*amp^2 := by dsimp only [Ce]; ring
      _ ≤ Ce*control^2*(1+Height)^(2*max nr nt)*Z^(R+ε)*amp^2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hntpow (mul_nonneg hCe (sq_nonneg control)))
            (Real.rpow_nonneg (zero_le_one.trans hZ) _)) (sq_nonneg amp)
      _ ≤ (Ce*control^2*(1+Height)^(2*max nr nt)*Z^(R+ε)*amp^2)*
          ((1+2*Real.log Y)*(3+T^(1/3 : ℝ))) :=
        le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hbox hterm)
      _ = _ := by dsimp only [E]; ring
  have hret := hretained Wlong hs Z R v y N T hZ hR hN hT hcap hv hy hmax href η m D rows χ ψ
    hon hoff hr hc hmod U (Z^(xi/2)) Y Xshort Height omega X t Wshort c d B F
    (by positivity) hY hXshort hHeight hX hU hYcap ht hd hB hshort hshortsmooth htest hlen
  have hrPaid : (∑ i : rows, ‖G i*(retained i*P i)‖^2) ≤ Cr*E := by
    have hmain : (∑ i : rows, ‖G i*(retained i*P i)‖^2) ≤
        Cr*(sourceControl Sr Wlong)^2*(1+Height)^(2*nr)*(1+2*Real.log Y)*
          Z^(R+ε)*(3+T^(1/3 : ℝ))*amp^2 := by
      simpa only [retained,P,amp,norm_mul,hG,one_mul,mul_assoc] using hret
    apply hmain.trans
    have hb0 : 0 ≤ 1+2*Real.log Y := zero_le_one.trans hbox
    have hprofileSquare : (sourceControl Sr Wlong)^2 ≤ control^2 :=
      pow_le_pow_left₀ (sourceControl_nonneg Sr Wlong) hSr 2
    have hhead : Cr*(sourceControl Sr Wlong)^2*(1+Height)^(2*nr) ≤
        Cr*control^2*(1+Height)^(2*max nr nt) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprofileSquare hCr.le) hnrpow
        (by positivity) (mul_nonneg hCr.le (sq_nonneg control))
    calc
      _ = (Cr*(sourceControl Sr Wlong)^2*(1+Height)^(2*nr))*
          ((1+2*Real.log Y)*Z^(R+ε)*(3+T^(1/3 : ℝ))*amp^2) := by ring
      _ ≤ (Cr*control^2*(1+Height)^(2*max nr nt))*
          ((1+2*Real.log Y)*Z^(R+ε)*(3+T^(1/3 : ℝ))*amp^2) :=
        mul_le_mul_of_nonneg_right hhead (by positivity)
      _ = _ := by dsimp only [E]; ring
  have hid (i : rows) : polynomial (χ i) false Wlong (X i) 0 (2*Real.pi*t i)*
      polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*∏ j, (F j).value (χ i) =
      G i*(retained i*P i)+err i*P i := by dsimp only [P,err]; ring
  simp_rw [hid]
  apply (split_energy (fun i => G i*(retained i*P i)) (fun i => err i*P i)).trans
  calc
    _ ≤ 2*(Cr*E)+2*(Ce*E) := add_le_add
      (mul_le_mul_of_nonneg_left hrPaid (by norm_num))
      (mul_le_mul_of_nonneg_left hePaid (by norm_num))
    _ = _ := by dsimp only [E,amp,control]; ring

end
end Candidate.SilPrior.FourthPower.ReferenceUniformOriginalEnergy
