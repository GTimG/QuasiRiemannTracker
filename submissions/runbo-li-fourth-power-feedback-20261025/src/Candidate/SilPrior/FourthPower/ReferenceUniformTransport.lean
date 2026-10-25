/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform homogeneous transport of the improved reference through the actual
direct/reflected selection and the forward frozen extraction. All ordinary
profile controls and constants precede the profile and the original data.
-/
import Candidate.SilPrior.FourthPower.ReferenceUniformOriginalEnergy
import Candidate.SilPrior.FourthPower.ReferenceExtractionGeometry
import Candidate.SilPrior.FourthPower.KernelReflectedEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.ReferenceUniformTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CanonicalQuadraticSieve CanonicalRowCompletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferenceFactors ReferenceHeckeProducts ReferenceExtractionGeometry
open ReferenceCrudeFactors ReferenceTailEnergy
open KernelAllocationIdentity KernelPhysicalScalars
open CenteredMomentScaleSupremum CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalPrimitive CenteredMomentOriginalReflectionApproximation
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

set_option maxHeartbeats 800000 in
theorem selected_reference (ε L K a b xi : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a) (hb : 0 ≤ b) (hxi : 0 < xi) :
    ∃ n : ℕ, ∃ Scontrol : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ Scontrol ∧
      ∀ Wlong : 𝓢(ℝ,ℂ), Function.support (Wlong : ℝ → ℂ) ⊆ Icc a b →
      ∀ (Z R v y T : ℝ),
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
        C*(sourceControl Scontrol Wlong)^2*(1+Height)^(2*n)*Z^(R+ε)*
          (3+T^(1/3 : ℝ))*(Real.sqrt d*B*∏ j, (F j).amplitude)^2 := by
  obtain ⟨nr,Sr,Cr,hCr,hSr0,hreflected⟩ :=
    ReferenceUniformOriginalEnergy.original_reference (α:=α) (ε/2) L K K a b xi
      (half_pos hε) hL hK ha hxi
  obtain ⟨ne,Se,Ct,hCt,hSe0,happrox⟩ :=
    ReferenceUniformApproximation.original_approximation a b xi (L+1) K K ha hxi hK
  obtain ⟨Cd,hCd,hdirect⟩ :=
    ReferenceProfileEnergy.two_smooth_product (α:=α) (ε/2) L (half_pos hε) hL
  let Scontrol := Sr ∪ Se
  let κ : ℝ := 128^(Fintype.card α+1)
  let Ce : ℝ := 128*(Ct*κ)^2
  let k := xi/2+K/2
  let Dlog := 1+2*Real.log 4+2*k/(ε/2)
  let Md := Cd*(Real.sqrt b)^2*(4/3)
  let Mr := Cr*Dlog*(4/3)
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hDlog : 0 < Dlog := by dsimp only [Dlog]; positivity
  have hMd : 0 ≤ Md := by dsimp only [Md]; positivity
  have hMr : 0 < Mr := by dsimp only [Mr]; positivity
  have hCe : 0 < Ce := by dsimp only [Ce,κ]; positivity
  have hS0 : (0,0) ∈ Scontrol := Finset.mem_union_left _ hSr0
  refine ⟨max nr ne,Scontrol,Md+Mr+Ce,by positivity,hS0,?_⟩
  intro Wlong hsupport Z R v y T hZ hR hv0 hy0 hT hcap hv hy η m D rows χ hon hoff hr hnonprincipal
  intro U X Xshort Height t omega Wshort c d B F hU hUcap hX hXshort hHeight ht hmod
  intro hd hB hshort hshortsmooth htest hvolume hmax href
  let Q := sourceControl Scontrol Wlong
  have hQ : 0 ≤ Q := sourceControl_nonneg Scontrol Wlong
  have hSr : sourceControl Sr Wlong ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left : Sr ⊆ Sr ∪ Se)) Wlong
  have hSe : sourceControl Se Wlong ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right : Se ⊆ Sr ∪ Se)) Wlong
  have hlong (x : ℝ) : ‖Wlong x‖ ≤ Q :=
    (SchwartzMap.norm_le_seminorm ℝ Wlong x).trans
      (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS0)
  let amp := Real.sqrt d*B*∏ j, (F j).amplitude
  let E := Q^2*(1+Height)^(2*max nr ne)*Z^(R+ε)*(3+T^(1/3 : ℝ))*amp^2
  let N := max 1 (branchCap b (Z^(xi/2)) X U*(d*Xshort)*∏ i, (F i).length)
  have hamp : 0 ≤ amp := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB)
    (Finset.prod_nonneg (fun i _ => (F i).amplitude_nonneg))
  have hZp := zero_lt_one.trans_le hZ
  have hE : 0 ≤ E := by dsimp only [E]; positivity
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
    simpa only [E,amp,Q,mul_assoc] using hh
  by_cases hsmall : X ≤ Real.sqrt U
  · have hlen : (b*X)*(d*Xshort)*(∏ i, (F i).length) ≤ N := by
      simpa only [N,branchCap,if_pos hsmall] using
        (le_max_right 1 (branchCap b (Z^(xi/2)) X U*(d*Xshort)*∏ i, (F i).length))
    have hh := hdirect Z R v y N (max 1 T) hZ hR hN hTr hcap hv hy hNs.1 hNs.2
      η m D rows χ hon hoff hr Wlong Wshort b d Q B X Xshort t omega F
      hb hd hQ hB hX hXshort hlong hshort0
      (fun x hx => (hsupport hx).2) (fun x hx => (hshort hx).2) hlen
    have hz : Z^(R+ε/2) ≤ (1+Height)^(2*max nr ne)*Z^(R+ε) :=
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg hZp.le _) hHpow)
    have he : Q^2*Z^(R+ε/2)*(3+(max 1 T)^(1/3 : ℝ))*amp^2 ≤ (4/3)*E := by
      calc
        _ ≤ Q^2*((1+Height)^(2*max nr ne)*Z^(R+ε))*
            ((4/3)*(3+T^(1/3 : ℝ)))*amp^2 := by gcongr
        _ = _ := by dsimp only [E]; ring
    have hh' : (∑ i : rows, ‖polynomial (χ i) false Wlong X 0 (2*Real.pi*t)*
        polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*∏ j, (F j).value (χ i)‖^2) ≤
        (Cd*(Real.sqrt b)^2)*(Q^2*Z^(R+ε/2)*(3+(max 1 T)^(1/3 : ℝ))*amp^2) := by
      apply hh.trans_eq
      dsimp only [amp]
      ring
    apply hh'.trans
    calc
      _ ≤ (Cd*(Real.sqrt b)^2)*((4/3)*E) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = Md*E := by dsimp only [Md]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE
  · have hlarge : Real.sqrt U < X := lt_of_not_ge hsmall
    have htail (i : rows) : ((χ i).modulus.absNorm : ℝ) ≤ Z^K*X :=
      reflected_tail_cap U X _ Z K hU hZp.le hlarge (hmodK i)
    let Y := 4*Z^(xi/2)*(U/X)
    by_cases hY : 1 ≤ Y
    · have hlen : Y*(d*Xshort)*(∏ i, (F i).length) ≤ N := by
        simpa only [Y,N,branchCap,if_neg hsmall] using
          (le_max_right 1 (branchCap b (Z^(xi/2)) X U*(d*Xshort)*∏ i, (F i).length))
      have hh := hreflected Wlong hsupport Z R v y N (max 1 T) hZ hR hN hTr hcap hv hy hNs.1 hNs.2
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
      have hSr2 : (sourceControl Sr Wlong)^2 ≤ Q^2 :=
        pow_le_pow_left₀ (sourceControl_nonneg Sr Wlong) hSr 2
      have he : (sourceControl Sr Wlong)^2*(1+Height)^(2*nr)*(1+2*Real.log Y)*Z^(R+ε/2)*
          (3+(max 1 T)^(1/3 : ℝ))*amp^2 ≤ (Dlog*(4/3))*E := by
        calc
          _ = (sourceControl Sr Wlong)^2*(1+Height)^(2*nr)*
              ((1+2*Real.log Y)*Z^(R+ε/2))*(3+(max 1 T)^(1/3 : ℝ))*amp^2 := by ring
          _ ≤ Q^2*(1+Height)^(2*max nr ne)*(Dlog*Z^(R+ε))*
              ((4/3)*(3+T^(1/3 : ℝ)))*amp^2 := by gcongr
          _ = _ := by dsimp only [E]; ring
      apply hh.trans
      calc
        _ = Cr*((sourceControl Sr Wlong)^2*(1+Height)^(2*nr)*(1+2*Real.log Y)*Z^(R+ε/2)*
            (3+(max 1 T)^(1/3 : ℝ))*amp^2) := by dsimp only [amp]; ring
        _ ≤ Cr*((Dlog*(4/3))*E) := mul_le_mul_of_nonneg_left he hCr.le
        _ = Mr*E := by dsimp only [Mr]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE
    · choose ψ G hprim hne hG hc he using fun i => happrox Wlong hsupport (χ i) (hnonprincipal i)
      let Pshort (i : rows) := polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*
        ∏ j, (F j).value (χ i)
      let erow (i : rows) := polynomial (χ i) false Wlong X 0 (2*Real.pi*t)
      have hP (i : rows) : ‖Pshort i‖ ≤ κ*Z^L*amp := by
        exact (smooth_product_norm (χ i) Wshort d B Xshort omega hd hB hXshort hshort0
          (fun x hx => (hshort hx).2) F).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvolume (by positivity)) hamp)
      have herr (i : rows) : ‖erow i‖ ≤ (Ct*Q)*(1+Height)^ne*Z^(-(L+1)) := by
        have hz := ReferenceRetainedGeometry.retainedOriginal_zero (χ i) (ψ i) Wlong
          X U (Z^(xi/2)) t hX (by positivity) (hc i) (hmod i) (lt_of_not_ge hY)
        have hh := he i X t Z hX hZ (hmodK i) (htail i)
        rw [hz,mul_zero,sub_zero] at hh
        apply hh.trans
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hSe hCt.le)
          (pow_le_pow_left₀ (by positivity) (by linarith) ne)
          (by positivity) (mul_nonneg hCt.le hQ)
      have hh := powered_error_energy rows erow Pshort Z R ε L (Ct*Q) κ Height amp ne
        hZ hR hε.le (mul_nonneg hCt.le hQ) (by positivity) hHeight hamp hr herr hP
      have he : Q^2*(1+Height)^(2*ne)*Z^(R+ε)*amp^2 ≤ E := by
        calc
          _ ≤ Q^2*(1+Height)^(2*max nr ne)*Z^(R+ε)*amp^2 := by gcongr
          _ ≤ (Q^2*(1+Height)^(2*max nr ne)*Z^(R+ε)*amp^2)*(3+T^(1/3 : ℝ)) :=
            le_mul_of_one_le_right (by positivity) hcost
          _ = _ := by dsimp only [E]; ring
      have hh' : (∑ i : rows, ‖polynomial (χ i) false Wlong X 0 (2*Real.pi*t)*
          polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*∏ j, (F j).value (χ i)‖^2) ≤
          Ce*(Q^2*(1+Height)^(2*ne)*Z^(R+ε)*amp^2) := by
        convert hh using 1
        · simp only [erow,Pshort,mul_assoc]
        · dsimp only [Ce]; ring
      exact hh'.trans ((mul_le_mul_of_nonneg_left he hCe.le).trans
        (mul_le_mul_of_nonneg_right (by linarith) hE))

variable {Frozen Live : Type*} [Fintype Frozen] [Fintype Live]

theorem forward_product_reference (ε L K a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 0 ≤ Bf) :
    ∃ n : ℕ, ∃ Scontrol : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ Scontrol ∧
      ∀ Wlong : 𝓢(ℝ,ℂ), Function.support (Wlong : ℝ → ℂ) ⊆ Icc a b →
      ∀ (Z R v y ratio : ℝ),
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
        C*(sourceControl Scontrol Wlong)^2*(1+Height)^(2*n)*Z^(R+ε)*A^2*(3+ratio^(1/3 : ℝ)) := by
  obtain ⟨n,Scontrol,Cr,hCr,hScontrol,hr⟩ := selected_reference (α:=Live) (ε/2) L K a b xi
    (half_pos hε) hL hK ha hb hxi
  obtain ⟨Cm,hCm,hm⟩ := KernelReflectedEnergy.actual_reflected_subpower (α:=Frozen) Bf
    (ε/(2*K)) hBf (div_pos hε (by positivity))
  refine ⟨n,Scontrol,Cm*Cr,mul_pos hCm hCr,hScontrol,?_⟩
  intro Wlong hs
  intro Z R v y ratio hZ hR hv0 hy0 hratio hcap hv hy η m D₀ rows χ hon hoff hrows hnonprincipal
  intro S hS F hinj D hd hsD pool β P hP hp hβ U Height A Wshort c d B
  intro hU hUcap hHeight hA hmod hd0 hB hshort hshortsmooth htest
  intro X Xshort t omega H hX ht hamp hvolume hmax href
  let G (j : Frozen → S) (e : Id × Id) (i : rows) :=
    polynomial (χ i) false Wlong (X j e) 0 (2*Real.pi*t j e)*
      polynomial (χ i) false Wshort (Xshort j e) 0 (2*Real.pi*omega j e)*
        ∏ k, (H j e k).value (χ i)
  let E := Cr*(sourceControl Scontrol Wlong)^2*(1+Height)^(2*n)*Z^(R+ε/2)*A^2*(3+ratio^(1/3 : ℝ))
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
    have hh := hr Wlong hs Z R v y (ratio*r) hZ hR hv0 hy0 (mul_nonneg hratio hr0) hcap hv hy η m D₀ rows χ hon hoff
      hrows hnonprincipal U (X j e) (Xshort j e) Height (t j e) (omega j e)
      Wshort c d B (H j e) hU hUcap (hX j hj e he).1 (hX j hj e he).2
      hHeight (ht j hj e he) hmod hd0 hB hshort hshortsmooth htest
      (hvolume j hj e he) (hmax j hj e he) (by simpa only [r,mul_assoc] using href j hj e he)
    have ha0 : 0 ≤ Real.sqrt d*B*∏ k, (H j e k).amplitude :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB)
        (Finset.prod_nonneg (fun k _ => (H j e k).amplitude_nonneg))
    apply hh.trans
    calc
      _ ≤ Cr*(sourceControl Scontrol Wlong)^2*(1+Height)^(2*n)*Z^(R+ε/2)*
          (3+(ratio*r)^(1/3 : ℝ))*A^2 := by
        gcongr
        exact hamp j hj e he
      _ ≤ Cr*(sourceControl Scontrol Wlong)^2*(1+Height)^(2*n)*Z^(R+ε/2)*
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
  have hsum : Z^(ε/2)*Z^(R+ε/2) = Z^(R+ε) := by
    rw [←Real.rpow_add hZp]
    congr 1
    ring
  apply hh.trans_eq
  rw [hpow]
  dsimp [E]
  calc
    _ = (Cm*Cr)*(sourceControl Scontrol Wlong)^2*(1+Height)^(2*n)*(Z^(ε/2)*Z^(R+ε/2))*A^2*(3+ratio^(1/3 : ℝ)) := by ring
    _ = _ := by rw [hsum]

end
end Candidate.SilPrior.FourthPower.ReferenceUniformTransport
