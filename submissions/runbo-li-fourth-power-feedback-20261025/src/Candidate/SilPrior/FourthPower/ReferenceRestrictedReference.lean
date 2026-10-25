/- Copyright (c) 2026 Sil. Apache-2.0.
Unconditional reference for the literal fifth-free marked family. All
frozen subsets, live injectivity, fixed cross-holes, natural frequencies
and the full frozen-product extraction ratio are retained.
-/
import Candidate.SilPrior.FourthPower.ReferenceForwardRows
import Candidate.SilPrior.FourthPower.ReferenceMarkedLengths
import Candidate.SilPrior.FourthPower.ReferenceKernelEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.ReferenceRestrictedReference
noncomputable section
open scoped Classical BigOperators ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CanonicalQuadraticSieve CanonicalRowCompletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferenceFactors ReferenceHeckeProducts ReferenceExtractionGeometry
open ReferenceMarkedLengths ReferenceForwardRows ReferencePrimeEnclosure
open KernelRowExpansion KernelRowProfiles KernelRowPools KernelPhysicalScalars
open KernelMarkedRows KernelAssignmentReindex
open CenteredMomentScaleSupremum
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

theorem child_geometry (b A X₁ X₂ U V d₁ d₂ f q : ℝ)
    (hb : 0 ≤ b) (hA : 1 ≤ A) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hd₁ : 1 ≤ d₁) (hd₂ : 0 < d₂) (hf : 1 ≤ f)
    (hq : 0 ≤ q) (hlen : q ≤ V/f) :
    b*(X₁/d₁)*q ≤ b*X₁*V ∧
    branchCap b A (X₂/d₂) U*(b*(X₁/d₁))*q ≤ (b+4)*A*b*X₁*V*Real.sqrt U ∧
    branchCap b A (X₂/d₂) U*(b*(X₁/d₁))*q ≤
      ((b+4)*A*b*(X₁*V*U/X₂))*(d₂/(d₁*f)) := by
  have h₁p := zero_lt_one.trans_le hd₁
  have hshort : X₁/d₁ ≤ X₁ := div_le_self hX₁.le hd₁
  have hlive : q ≤ V := hlen.trans (div_le_self hV hf)
  have hc0 := branchCap_nonneg b A (X₂/d₂) U hb (zero_le_one.trans hA) (div_pos hX₂ hd₂) hU
  have hbase := extracted_bounds b A X₁ X₂ U V d₁ d₂ f hb hA hX₁ hX₂ hU hV hd₁ hd₂ hf
  have he : branchCap b A (X₂/d₂) U*(b*(X₁/d₁))*q ≤
      b*((X₁/d₁)*branchCap b A (X₂/d₂) U*(V/f)) := by
    calc
      _ ≤ branchCap b A (X₂/d₂) U*(b*(X₁/d₁))*(V/f) :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = _ := by ring
  refine ⟨mul_le_mul (mul_le_mul_of_nonneg_left hshort hb) hlive hq (by positivity),?_,?_⟩
  · exact (he.trans (mul_le_mul_of_nonneg_left hbase.1 hb)).trans_eq (by ring)
  · exact (he.trans (mul_le_mul_of_nonneg_left hbase.2 hb)).trans_eq (by ring)

theorem restricted_reference (ε L K a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
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
      ∀ (U X₁ X₂ Height t₁ t₂ : ℝ) (Wshort : ℝ → ℂ) (B : ℝ),
      1 ≤ U → U ≤ Z^K → 0 < X₁ → 0 < X₂ → 0 ≤ Height → ‖t₂‖ ≤ Height →
      (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ U) →
      0 ≤ B → Function.support Wshort ⊆ Icc a b → ContDiff ℝ ∞ Wshort →
      (∀ (j : Fin 2) (x : ℝ), ‖scaleTest Wshort j x‖ ≤ B) →
      ∀ (S : Finset PrimeIdeal),
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ Z^K) →
      (∀ I, Supported I →
        ((Ideal.absNorm I : ℝ) ≤ b*X₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues S) →
      ∀ (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ Bf) →
      (∏ i, 2*P i) ≤ Z^L → b*X₁*(∏ i, 2*P i) ≤ Z^L →
      (b+4)*Z^(xi/2)*b*X₁*(∏ i, 2*P i)*Real.sqrt U ≤ Z^v →
      (b+4)*Z^(xi/2)*b*(X₁*(∏ i, 2*P i)*U/X₂) ≤ Z^y*ratio →
      (∑ i : rows, ‖weightedSum (naturalCoefficients (χ i) S pool β P)
        (fun slot => normalizedRow (χ i) (supportedRectangle S b X₁ X₂)
          (sourceValue false S slot) (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) X₁ X₂)‖^2) ≤
        C*(1+Height)^(2*n)*Z^(R+ε)*B^2*(3+ratio^(1/3 : ℝ)) := by
  let δ := ε/(4*L)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨M,hM,hfactor⟩ := uniform_remaining_factor (α:=α) δ hδ
  choose nT hnT using fun T : Finset α =>
    ReferenceKernelEnergy.forward_product_reference (Frozen:=T) (Live:=Unit)
      (ε/2) L K a b xi Bf (half_pos hε) hL hK ha hb hxi (zero_le_one.trans hBf)
  let n := ∑ T : Finset α, nT T
  have hn (T : Finset α) : nT T ≤ n :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ T)
  refine ⟨n,?_⟩
  intro Wlong hlong hlongsmooth
  choose Cr hCr hr using fun T : Finset α => hnT T Wlong hlong hlongsmooth
  let Cmax := 1+∑ T : Finset α, Cr T
  have hCmax : 0 < Cmax := by
    have hh := Finset.sum_nonneg (fun T (_ : T ∈ (Finset.univ : Finset (Finset α))) => (hCr T).le)
    dsimp [Cmax]; linarith
  have hCrmax (T : Finset α) : Cr T ≤ Cmax := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=Cr) (fun T _ => (hCr T).le) (Finset.mem_univ T)
    dsimp [Cmax]; linarith
  let Cbase := Real.sqrt b*M*(Real.sqrt 2*Bf)^Fintype.card α
  let Camp := 1+Cbase^2
  have hCbase : 0 ≤ Cbase := by dsimp [Cbase]; positivity
  have hCamp : 0 < Camp := by dsimp [Camp]; positivity
  refine ⟨(Fintype.card (Finset α) : ℝ)^2*Cmax*Camp,by positivity,?_⟩
  intro Z R v y ratio hZ hR hv0 hy0 hratio hcap hv hy η m D₀ rows χ hon hoff hrows hnonprincipal
  intro U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hX₁ hX₂ hHeight ht₂ hmod hB hshort hshortsmooth htest
  intro S hS henclose pool β P hP hp hβ hVcap hvolume hmax href
  let V := ∏ i, 2*P i
  have hV : 0 ≤ V := Finset.prod_nonneg (fun i _ => by have := hP i; positivity)
  have hZp := zero_lt_one.trans_le hZ
  have hZL : 1 ≤ Z^L := Real.one_le_rpow hZ hL.le
  have hmaxV : max 1 V ≤ Z^L := max_le hZL hVcap
  have hVpower : (max 1 V)^δ ≤ Z^(ε/4) := by
    have hh := Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hmaxV hδ.le
    rw [← Real.rpow_mul hZp.le] at hh
    have he : L*δ = ε/4 := by dsimp [δ]; field_simp
    simpa only [he] using hh
  choose H hHlen hHcaps hHvalue using fun (T : Finset α) (t : T → S) =>
    hfactor T S pool β P Bf hBf hP hp hβ t
  let A := Real.sqrt b*B*(M*(max 1 V)^δ*(Real.sqrt 2*Bf)^Fintype.card α)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAupper : A ≤ Cbase*B*Z^(ε/4) := by
    calc
      _ ≤ Real.sqrt b*B*(M*Z^(ε/4)*(Real.sqrt 2*Bf)^Fintype.card α) := by dsimp [A]; gcongr
      _ = _ := by dsimp [Cbase]; ring
  have hA2 : A^2 ≤ Camp*B^2*Z^(ε/2) := by
    calc
      _ ≤ (Cbase*B*Z^(ε/4))^2 := pow_le_pow_left₀ hA hAupper 2
      _ = Cbase^2*B^2*Z^(ε/2) := by
        rw [mul_pow,mul_pow,← Real.rpow_natCast (Z^(ε/4)) 2,← Real.rpow_mul hZp.le]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp [Camp]; linarith) (sq_nonneg B)) (Real.rpow_nonneg hZp.le _)
  let E := Cmax*Camp*(1+Height)^(2*n)*Z^(R+ε)*B^2*(3+ratio^(1/3 : ℝ))
  let F (T : Finset α) (i : rows) :=
    ∑ t ∈ validFrozen T S pool, ∑ e ∈ divisorPool (supportedRectangle S b X₁ X₂),
      scalar (χ i) S (ordinarySeriesFor false) (markedSeriesFor false)
        (fun j : T => pool j.val) (fun j : T => β j.val) (fun j : T => P j.val) t e *
        (polynomial (χ i) false Wlong (X₂/Ideal.absNorm e.2) 0 (2*Real.pi*t₂)*
          polynomial (χ i) false Wshort (X₁/Ideal.absNorm e.1) 0 (2*Real.pi*t₁)*(H T t).value (χ i))
  have hgeometry (T : Finset α) (t : T → S) (ht : t ∈ validFrozen T S pool)
      (e : Id × Id) (he : e ∈ divisorPool (supportedRectangle S b X₁ X₂)) :=
    child_geometry b (Z^(xi/2)) X₁ X₂ U V (Ideal.absNorm e.1) (Ideal.absNorm e.2)
      (frozenNorm S t) (H T t).length hb (Real.one_le_rpow hZ (by positivity)) hX₁ hX₂
      (zero_le_one.trans hU) hV (ideal_norm_one_le (divisor_supported he).1)
      (zero_lt_one.trans_le (ideal_norm_one_le (divisor_supported he).2.1))
      (frozenNorm_one_le S T t) (H T t).length_nonneg
      ((hHcaps T t (Finset.mem_filter.mp ht).2.2).1)
  have henergy (T : Finset α) : (∑ i : rows, ‖F T i‖^2) ≤ E := by
    have hh := hr T Z R v y ratio hZ hR hv0 hy0 hratio hcap hv hy η m D₀ rows χ hon hoff hrows hnonprincipal
      S hS (validFrozen T S pool) (fun t ht => (Finset.mem_filter.mp ht).2.1)
      (fun _ => divisorPool (supportedRectangle S b X₁ X₂))
      (fun _ _ e he => ⟨(divisor_supported he).1,(divisor_supported he).2.1⟩)
      (fun _ _ e he => (divisor_supported he).2.2)
      (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val)
      (fun i => hP i.val) (fun i => hp i.val) (fun i => hβ i.val)
      U Height A Wshort a b B hU hUcap hHeight hA hmod hb hB hshort hshortsmooth htest
      (fun _ e => X₂/(Ideal.absNorm e.2 : ℝ)) (fun _ e => X₁/(Ideal.absNorm e.1 : ℝ))
      (fun _ _ => t₂) (fun _ _ => t₁) (fun t _ (_ : Unit) => H T t) (by
        intro t ht e he
        exact ⟨(shortened_positive_le hX₂ (divisor_supported he).2.1).1,
          (shortened_positive_le hX₁ (divisor_supported he).1).1⟩)
      (fun _ _ _ _ => ht₂) (by
        intro t ht e he
        have hh := mul_le_mul_of_nonneg_left
          (hHcaps T t (Finset.mem_filter.mp ht).2.2).2 (mul_nonneg (Real.sqrt_nonneg b) hB)
        simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_unique,pow_one,A,V] using hh) (by
        intro t ht e he
        simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_unique,pow_one] using
          (hgeometry T t ht e he).1.trans hvolume) (by
        intro t ht e he
        simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_unique,pow_one] using
          (hgeometry T t ht e he).2.1.trans hmax) (by
        intro t ht e he
        have hratio : 0 ≤ (Ideal.absNorm e.2 : ℝ)/
            ((Ideal.absNorm e.1 : ℝ)*frozenNorm S t) := by have := frozenNorm_pos S t; positivity
        simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_unique,pow_one] using
          (hgeometry T t ht e he).2.2.trans (mul_le_mul_of_nonneg_right href hratio))
    have hh' : (∑ i : rows, ‖F T i‖^2) ≤
        Cr T*(1+Height)^(2*nT T)*Z^(R+ε/2)*A^2*(3+ratio^(1/3 : ℝ)) := by
      simpa only [F,Finset.prod_const,Finset.card_univ,Fintype.card_unique,pow_one] using hh
    have hnpow : (1+Height)^(2*nT T) ≤ (1+Height)^(2*n) :=
      pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left 2 (hn T))
    apply hh'.trans
    calc
      _ ≤ Cr T*(1+Height)^(2*nT T)*Z^(R+ε/2)*(Camp*B^2*Z^(ε/2))*(3+ratio^(1/3 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA2 (by have := hCr T; positivity)) (by positivity)
      _ ≤ Cmax*(1+Height)^(2*n)*Z^(R+ε/2)*(Camp*B^2*Z^(ε/2))*(3+ratio^(1/3 : ℝ)) := by
        gcongr
        exact hCrmax T
      _ = Cmax*Camp*(1+Height)^(2*n)*(Z^(R+ε/2)*Z^(ε/2))*B^2*(3+ratio^(1/3 : ℝ)) := by ring
      _ = E := by
        rw [← Real.rpow_add hZp]
        dsimp [E]
        congr 3
        congr 1
        ring
  have hid (i : rows) : weightedSum (naturalCoefficients (χ i) S pool β P)
      (fun slot => normalizedRow (χ i) (supportedRectangle S b X₁ X₂)
        (sourceValue false S slot) (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) X₁ X₂) =
      ∑ T : Finset α, F T i := by
    simpa only [F] using forward_expansion S pool β P Wshort Wlong b X₁ X₂ t₁ t₂ hb hX₁ hX₂
      (fun x hx => (hshort hx).2) (fun x hx => (hlong hx).2) H hHvalue (χ i) (hoff i) henclose
  simp_rw [hid]
  apply (KernelCollisionEnergy.sum_family_energy (Finset.univ : Finset rows) F E henergy).trans_eq
  dsimp [E]
  ring

end
end Candidate.SilPrior.FourthPower.ReferenceRestrictedReference
