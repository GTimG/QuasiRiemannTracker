/- Copyright (c) 2026 Sil. Apache-2.0.
One unconditional reference for both the original and reflected branches.
The actual short retained range and the whole-column rounding are distinct.
-/
import Candidate.SilPrior.FourthPower.ReferenceEmptyEnergy
import Candidate.SilPrior.FourthPower.ReferenceExtractionGeometry

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReferenceSelectedEnergy
noncomputable section
open scoped Classical BigOperators ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CanonicalQuadraticSieve CanonicalRowCompletion
open ReferenceFactors ReferenceHeckeProducts ReferenceExtractionGeometry
open CenteredMomentScaleSupremum
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]

theorem selected_reference (ε L K a b xi : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a) (hb : 0 ≤ b) (hxi : 0 < xi) :
    ∃ n : ℕ, ∀ Wlong : ℝ → ℂ,
      Function.support Wlong ⊆ Icc a b → ContDiff ℝ ∞ Wlong →
      ∃ C : ℝ, 0 < C ∧ ∀ (Z R v y T : ℝ),
      1 ≤ Z → 0 ≤ R → 0 ≤ v → 0 ≤ y → 0 ≤ T →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 →
      ∀ (η : Character) (m D : O) (rows : Finset O) (χ : rows → Character),
      (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D I*idealRowHom x.val I) →
      (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ i, (χ i).residue ≠ 1) →
      ∀ (U X Xshort Height t omega : ℝ) (Wshort : ℝ → ℂ)
        (c d B : ℝ) (F : α → Factor),
      1 ≤ U → U ≤ Z^K → 0 < X → 0 < Xshort → 0 ≤ Height → ‖t‖ ≤ Height →
      (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ U) →
      0 ≤ d → 0 ≤ B → Function.support Wshort ⊆ Icc c d → ContDiff ℝ ∞ Wshort →
      (∀ (j : Fin 2) (x : ℝ), ‖scaleTest Wshort j x‖ ≤ B) →
      d*Xshort*(∏ i, (F i).length) ≤ Z^L →
      branchCap b (Z^(xi/2)) X U*(d*Xshort)*(∏ i, (F i).length) ≤ Z^v →
      branchCap b (Z^(xi/2)) X U*(d*Xshort)*(∏ i, (F i).length) ≤ Z^y*T →
      (∑ i : rows, ‖polynomial (χ i) false Wlong X 0 (2*Real.pi*t)*
        polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*
          ∏ j, (F j).value (χ i)‖^2) ≤
        C*(1+Height)^(2*n)*Z^(R+ε)*(3+T^(1/3 : ℝ))*
          (Real.sqrt d*B*∏ j, (F j).amplitude)^2 := by
  obtain ⟨nr,hnr⟩ := ReferenceOriginalEnergy.original_reference (α:=α) (ε/2) L K K a b xi
    (half_pos hε) hL hK ha hxi
  obtain ⟨ne,hne⟩ := ReferenceEmptyEnergy.empty_reference (α:=α) ε L K K a b xi hε.le hK ha hxi
  obtain ⟨Cd,hCd,hdirect⟩ := ReferenceProfileEnergy.two_smooth_product (α:=α) (ε/2) L (half_pos hε) hL
  refine ⟨max nr ne,?_⟩
  intro Wlong hsupport hW
  obtain ⟨Cr,hCr,hreflected⟩ := hnr Wlong hsupport hW
  obtain ⟨Ce,hCe,hempty⟩ := hne Wlong hsupport hW
  obtain ⟨B₀,hB₀,hB₀test⟩ := ReferenceProfileEnergy.bounded_scaleTests Wlong a b hsupport hW
  let k := xi/2+K/2
  let Dlog := 1+2*Real.log 4+2*k/(ε/2)
  let Md := Cd*(Real.sqrt b*B₀)^2*(4/3)
  let Mr := Cr*Dlog*(4/3)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hDlog : 0 < Dlog := by dsimp [Dlog]; positivity
  have hMd : 0 ≤ Md := by dsimp [Md]; positivity
  have hMr : 0 < Mr := by dsimp [Mr]; positivity
  refine ⟨Md+Mr+Ce,by positivity,?_⟩
  intro Z R v y T hZ hR hv0 hy0 hT hcap hv hy η m D rows χ hon hoff hr hnonprincipal
  intro U X Xshort Height t omega Wshort c d B F hU hUcap hX hXshort hHeight ht hmod
  intro hd hB hshort hshortsmooth htest hvolume hmax href
  let amp := Real.sqrt d*B*∏ j, (F j).amplitude
  let E := (1+Height)^(2*max nr ne)*Z^(R+ε)*(3+T^(1/3 : ℝ))*amp^2
  let N := max 1 (branchCap b (Z^(xi/2)) X U*(d*Xshort)*∏ i, (F i).length)
  have hamp : 0 ≤ amp := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB)
    (Finset.prod_nonneg (fun i _ => (F i).amplitude_nonneg))
  have hZp := zero_lt_one.trans_le hZ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hN : 1 ≤ N := le_max_left _ _
  have hNs := whole_length_caps Z v y _ T hZ hv0 hy0 hmax href
  have hTr : 0 ≤ max 1 T := zero_le_one.trans (le_max_left _ _)
  have hTcost := rounded_critical_cost T hT
  have hcost : 1 ≤ 3+T^(1/3 : ℝ) := by have := Real.rpow_nonneg hT (1/3 : ℝ); linarith
  have hHpow : 1 ≤ (1+Height)^(2*max nr ne) := one_le_pow₀ (by linarith)
  have hnrpow : (1+Height)^(2*nr) ≤ (1+Height)^(2*max nr ne) :=
    pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left 2 (Nat.le_max_left nr ne))
  have hnepow : (1+Height)^(2*ne) ≤ (1+Height)^(2*max nr ne) :=
    pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left 2 (Nat.le_max_right nr ne))
  have hmodK (i : rows) : ((χ i).modulus.absNorm : ℝ) ≤ Z^K := (hmod i).trans hUcap
  have hshort0 : ∀ x, ‖Wshort x‖ ≤ B := fun x => by
    simpa only [scaleTest,ite_true] using htest 0 x
  suffices hh : (∑ i : rows, ‖polynomial (χ i) false Wlong X 0 (2*Real.pi*t)*
      polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*∏ j, (F j).value (χ i)‖^2) ≤
      (Md+Mr+Ce)*E by
    simpa only [E,amp,mul_assoc] using hh
  by_cases hsmall : X ≤ Real.sqrt U
  · have hlen : (b*X)*(d*Xshort)*(∏ i, (F i).length) ≤ N := by
      simpa only [N,branchCap,if_pos hsmall] using
        (le_max_right 1 (branchCap b (Z^(xi/2)) X U*(d*Xshort)*∏ i, (F i).length))
    have hh := hdirect Z R v y N (max 1 T) hZ hR hN hTr hcap hv hy hNs.1 hNs.2
      η m D rows χ hon hoff hr Wlong Wshort b d B₀ B X Xshort t omega F
      hb hd hB₀.le hB hX hXshort
      (fun x => by simpa only [scaleTest,ite_true] using hB₀test 0 x) hshort0
      (fun x hx => (hsupport hx).2) (fun x hx => (hshort hx).2) hlen
    have hz : Z^(R+ε/2) ≤ (1+Height)^(2*max nr ne)*Z^(R+ε) :=
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg hZp.le _) hHpow)
    have he : Z^(R+ε/2)*(3+(max 1 T)^(1/3 : ℝ))*amp^2 ≤ (4/3)*E := by
      calc
        _ ≤ ((1+Height)^(2*max nr ne)*Z^(R+ε))*((4/3)*(3+T^(1/3 : ℝ)))*amp^2 := by gcongr
        _ = _ := by dsimp [E]; ring
    have hh' : (∑ i : rows, ‖polynomial (χ i) false Wlong X 0 (2*Real.pi*t)*
        polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*∏ j, (F j).value (χ i)‖^2) ≤
        (Cd*(Real.sqrt b*B₀)^2)*(Z^(R+ε/2)*(3+(max 1 T)^(1/3 : ℝ))*amp^2) := by
      apply hh.trans_eq
      dsimp [amp]
      ring
    apply hh'.trans
    calc
      _ ≤ (Cd*(Real.sqrt b*B₀)^2)*((4/3)*E) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = Md*E := by dsimp [Md]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE
  · have hlarge : Real.sqrt U < X := lt_of_not_ge hsmall
    have htail (i : rows) : ((χ i).modulus.absNorm : ℝ) ≤ Z^K*X :=
      reflected_tail_cap U X _ Z K hU hZp.le hlarge (hmodK i)
    let Y := 4*Z^(xi/2)*(U/X)
    by_cases hY : 1 ≤ Y
    · have hlen : Y*(d*Xshort)*(∏ i, (F i).length) ≤ N := by
        simpa only [Y,N,branchCap,if_neg hsmall] using
          (le_max_right 1 (branchCap b (Z^(xi/2)) X U*(d*Xshort)*∏ i, (F i).length))
      have hh := hreflected Z R v y N (max 1 T) hZ hR hN hTr hcap hv hy hNs.1 hNs.2
        η m D rows χ hon hoff hr hnonprincipal hmodK U Y Xshort Height omega
        (fun _ => X) (fun _ => t) Wshort c d B F hY hXshort hHeight (fun _ => hX)
        hmod (fun _ => le_rfl) htail (fun _ => ht) hd hB hshort hshortsmooth htest hlen
      have hratio : U/X ≤ Real.sqrt U := (div_le_iff₀ hX).mpr (by
        have hu0 := zero_le_one.trans hU
        have hs := Real.sqrt_nonneg U
        have hs2 := Real.sq_sqrt hu0
        nlinarith)
      have hYcap : Y ≤ 4*Z^k := by
        calc
          _ ≤ 4*Z^(xi/2)*Real.sqrt U := mul_le_mul_of_nonneg_left hratio (by positivity)
          _ ≤ 4*Z^(xi/2)*Real.sqrt (Z^K) := by gcongr
          _ = _ := by rw [sqrt_power Z K hZp.le,mul_assoc,← Real.rpow_add hZp]
      have hlog := log_box_absorbed Z Y 4 k R ε hZ hY (by norm_num) hk hε hYcap
      have hlogY0 : 0 ≤ 1+2*Real.log Y := by linarith [Real.log_nonneg hY]
      have he : (1+Height)^(2*nr)*(1+2*Real.log Y)*Z^(R+ε/2)*
          (3+(max 1 T)^(1/3 : ℝ))*amp^2 ≤ (Dlog*(4/3))*E := by
        calc
          _ = (1+Height)^(2*nr)*((1+2*Real.log Y)*Z^(R+ε/2))*
              (3+(max 1 T)^(1/3 : ℝ))*amp^2 := by ring
          _ ≤ (1+Height)^(2*max nr ne)*(Dlog*Z^(R+ε))*
              ((4/3)*(3+T^(1/3 : ℝ)))*amp^2 := by gcongr
          _ = _ := by dsimp [E]; ring
      apply hh.trans
      calc
        _ = Cr*((1+Height)^(2*nr)*(1+2*Real.log Y)*Z^(R+ε/2)*
            (3+(max 1 T)^(1/3 : ℝ))*amp^2) := by dsimp [amp]; ring
        _ ≤ Cr*((Dlog*(4/3))*E) := mul_le_mul_of_nonneg_left he hCr.le
        _ = Mr*E := by dsimp [Mr]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE
    · have hh := hempty Z R hZ hR rows χ hr hnonprincipal hmodK U Xshort Height omega
        (fun _ => X) (fun _ => t) Wshort d B F hXshort hHeight (fun _ => hX) hmod
        (fun _ => lt_of_not_ge hY) htail (fun _ => ht) hd hB
        (fun x hx => (hshort hx).2) hshort0 hvolume
      have he : (1+Height)^(2*ne)*Z^(R+ε)*amp^2 ≤ E := by
        calc
          _ ≤ (1+Height)^(2*max nr ne)*Z^(R+ε)*amp^2 := by gcongr
          _ ≤ ((1+Height)^(2*max nr ne)*Z^(R+ε)*amp^2)*(3+T^(1/3 : ℝ)) :=
            le_mul_of_one_le_right (by positivity) hcost
          _ = _ := by dsimp [E]; ring
      apply hh.trans
      calc
        _ = Ce*((1+Height)^(2*ne)*Z^(R+ε)*amp^2) := by dsimp [amp]; ring
        _ ≤ Ce*E := mul_le_mul_of_nonneg_left he hCe.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE

end
end Candidate.SilPrior.FourthPower.ReferenceSelectedEnergy
