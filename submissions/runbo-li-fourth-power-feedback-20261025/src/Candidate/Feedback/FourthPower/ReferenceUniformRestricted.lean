/- Copyright (c) 2026 Sil. Apache-2.0.
Homogeneous uniform reference through actual frozen-subset restriction and
common punctures. Controls and constants precede every Schwartz profile.

-/
import Candidate.Feedback.FourthPower.ReferenceUniformTransport
import Candidate.Feedback.FourthPower.ReferenceRestrictedReference
import Candidate.Feedback.FourthPower.ReferencePuncturedReference
import Candidate.Feedback.FourthPower.MixedFirstPuncturedReference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.ReferenceUniformRestricted
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CanonicalQuadraticSieve CanonicalRowCompletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferenceFactors ReferenceHeckeProducts ReferenceExtractionGeometry
open ReferenceMarkedLengths ReferenceForwardRows ReferencePrimeEnclosure
open ReferenceRestrictedReference
open KernelRowExpansion KernelRowProfiles KernelRowPools KernelPhysicalScalars
open KernelMarkedRows KernelAssignmentReindex KernelLabelledSlots KernelPunctureRows
open CenteredMomentScaleSupremum CenteredMomentFiniteProfileExceptional
open MixedFirstReferenceChoice MixedFirstPuncturedReference MixedFirstSeededSource
open MixedCanonicalSource MixedCenteredEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

/-- Uniformity survives all frozen subsets: their finite union of
controls, maximum-by-sum degree, and common constant are chosen before W. -/
theorem restricted_reference (ε L K a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
    ∃ n : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ Wlong : 𝓢(ℝ,ℂ), Function.support (Wlong : ℝ → ℂ) ⊆ Icc a b →
      ∀ (Z R v y ratio : ℝ),
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
        C*(sourceControl control Wlong)^2*(1+Height)^(2*n)*Z^(R+ε)*B^2*
          (3+ratio^(1/3 : ℝ)) := by
  let δ := ε/(4*L)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨M,hM,hfactor⟩ := uniform_remaining_factor (α:=α) δ hδ
  choose nT controlT Cr hCr h00T hr using fun T : Finset α =>
    ReferenceUniformTransport.forward_product_reference (Frozen:=T) (Live:=Unit)
      (ε/2) L K a b xi Bf (half_pos hε) hL hK ha hb hxi (zero_le_one.trans hBf)
  let n := ∑ T : Finset α, nT T
  have hn (T : Finset α) : nT T ≤ n :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ T)
  let control := (Finset.univ : Finset (Finset α)).biUnion controlT
  have hcontrol (T : Finset α) : controlT T ⊆ control :=
    Finset.subset_biUnion_of_mem controlT (Finset.mem_univ T)
  have h00 : (0,0) ∈ control := hcontrol ∅ (h00T ∅)
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
  refine ⟨n,control,(Fintype.card (Finset α) : ℝ)^2*Cmax*Camp,by positivity,h00,?_⟩
  intro Wlong hlong
  have hprofile (T : Finset α) : sourceControl (controlT T) Wlong ≤ sourceControl control Wlong :=
    Seminorm.le_def.mp (Finset.sup_mono (hcontrol T)) Wlong
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
  let E := Cmax*Camp*(sourceControl control Wlong)^2*(1+Height)^(2*n)*Z^(R+ε)*B^2*
    (3+ratio^(1/3 : ℝ))
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
    have hh := hr T Wlong hlong Z R v y ratio hZ hR hv0 hy0 hratio hcap hv hy η m D₀ rows χ hon hoff hrows hnonprincipal
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
        Cr T*(sourceControl (controlT T) Wlong)^2*(1+Height)^(2*nT T)*Z^(R+ε/2)*A^2*
          (3+ratio^(1/3 : ℝ)) := by
      simpa only [F,Finset.prod_const,Finset.card_univ,Fintype.card_unique,pow_one] using hh
    have hnpow : (1+Height)^(2*nT T) ≤ (1+Height)^(2*n) :=
      pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left 2 (hn T))
    have hcp : Cr T*(sourceControl (controlT T) Wlong)^2 ≤
        Cmax*(sourceControl control Wlong)^2 :=
      mul_le_mul (hCrmax T)
        (pow_le_pow_left₀ (sourceControl_nonneg _ _) (hprofile T) 2)
        (sq_nonneg _) hCmax.le
    apply hh'.trans
    calc
      _ ≤ Cr T*(sourceControl (controlT T) Wlong)^2*(1+Height)^(2*nT T)*Z^(R+ε/2)*
          (Camp*B^2*Z^(ε/2))*(3+ratio^(1/3 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA2 (by have := hCr T; positivity)) (by positivity)
      _ ≤ Cmax*(sourceControl control Wlong)^2*(1+Height)^(2*n)*Z^(R+ε/2)*
          (Camp*B^2*Z^(ε/2))*(3+ratio^(1/3 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul hcp hnpow (by positivity) (mul_nonneg hCmax.le (sq_nonneg _)))
              (Real.rpow_nonneg hZp.le _))
            (by positivity)) (by positivity)
      _ = Cmax*Camp*(sourceControl control Wlong)^2*(1+Height)^(2*n)*
          (Z^(R+ε/2)*Z^(ε/2))*B^2*(3+ratio^(1/3 : ℝ)) := by ring
      _ = E := by
        rw [← Real.rpow_add hZp]
        simp only [show R+ε/2+ε/2 = R+ε by ring,E]
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


/-- Puncturing retains the same homogeneous profile square and the
original ratio saving; its positive divisor sum costs only the old Z^ε. -/
theorem punctured_reference (ε L K a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
    ∃ n : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ Wlong : 𝓢(ℝ,ℂ), Function.support (Wlong : ℝ → ℂ) ⊆ Icc a b →
      ∀ (Z R v y : ℝ),
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
        C*(sourceControl control Wlong)^2*(1+Height)^(2*n)*Z^(R+ε)*B^2 := by
  obtain ⟨n,control,Cr,hCr,h00,hr⟩ := ReferenceUniformRestricted.restricted_reference (α:=α)
    (ε/2) L K a b xi Bf (half_pos hε) hL hK ha hb hxi hBf
  obtain ⟨Cm,hCm,hm⟩ := KernelPunctureFamily.energy K (ε/2) hK.le (half_pos hε)
  refine ⟨n,control,Cm*Cr,mul_pos hCm hCr,h00,?_⟩
  intro Wlong hlong
  have hr := hr Wlong hlong
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
  let E := Cr*(sourceControl control Wlong)^2*(1+Height)^(2*n)*Z^(R+ε/2)*B^2
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
    _ = (Cm*Cr)*(sourceControl control Wlong)^2*(1+Height)^(2*n)*
        (Z^(ε/2)*Z^(R+ε/2))*B^2 := by ring
    _ = _ := by
      rw [← Real.rpow_add hZp]
      simp only [show ε/2+(R+ε/2) = R+ε by ring]


variable {ι : Type*} [Fintype ι]

/-- The same short/reference geometry with genuinely profile-uniform
constants. Canonical deletions supply the hole zeros before any norm. -/
theorem short_punctured_reference (ε L K a b xi Bf : ℝ)
    (hε : 0<ε) (hL : 0<L) (hK : 0<K) (ha : 0<a)
    (hb : 0 ≤ b) (hxi : 0<xi) (hBf : 1 ≤ Bf) :
    ∃ n : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ Wlong : 𝓢(ℝ,ℂ), Function.support (Wlong : ℝ → ℂ) ⊆ Icc a b →
      ∀ Z R P s d l δ : ℝ,
      1 ≤ Z → 0 ≤ R → 0 ≤ s → 0 ≤ d → 0 ≤ l → 0 ≤ δ → P+2*s+4*d<R →
      R+(l+(R+d)/2+s+2*δ) ≤ L →
      l+(R+d)/2+s+2*δ ≤ (4/5)*R → R+d+2*l-P+s+2*δ ≤ R/2 →
      (b+4)*b*(2:ℝ)^Fintype.card ι ≤ Z^δ → xi/2 ≤ δ →
      ∀(η : Character)(m D₀ : HeckeFamily.O)(rows : Finset HeckeFamily.O)(χ : rows → Character),
      (∀x I,Supported I → idealCoeff (χ x) I=fixedCoefficient η m D₀ I*idealRowHom x.val I) →
      (∀x I,¬Supported I → idealCoeff (χ x) I=0) →
      (∀x∈rows,(Ideal.absNorm (Ideal.span {x}):ℝ) ≤ Z^R) →
      (∀i,(χ i).residue ≠ 1) →
      ∀(U X₁ X₂ Height t₁ t₂ : ℝ)(Wshort : ℝ → ℂ)(B : ℝ),
      1 ≤ U → U ≤ Z^K → U ≤ Z^(R+d) → 0<X₁ → 0<X₂ → X₁*X₂=Z^P → X₁ ≤ Z^l →
      0 ≤ Height → ‖t₂‖ ≤ Height → (∀i,((χ i).modulus.absNorm:ℝ) ≤ U) →
      0 ≤ B → Function.support Wshort⊆Icc a b → ContDiff ℝ ∞ Wshort →
      (∀(j : Fin 2)(x : ℝ),‖scaleTest Wshort j x‖ ≤ B) →
      ∀(S H : Finset PrimeIdeal)(F : Id),F ≠ 0 → (F.absNorm:ℝ) ≤ Z^K →
      (∀Q∈H,Q.val∣F) →
      (∀Q∈S,Supported Q.val ∧ (Q.val.absNorm:ℝ) ≤ Z^K) →
      (∀I,Supported I → ((I.absNorm:ℝ) ≤ b*X₁ ∨ (I.absNorm:ℝ) ≤ b*X₂) →
        primeSupport I⊆primeValues S) →
      ∀(pool : ι → Finset Id)(ν : ι → Character)(R₀ : ι → Finset Id)
        (t : ℝ)(Wslot : ι → ℝ → ℂ)(scales : ι → ℝ),
      (∀i,0<scales i) →
      (∀i I,I∈pool i → Supported I ∧ (I.absNorm:ℝ) ≤ 2*scales i) →
      (∀i I,I∈pool i → ‖slotCoefficient ν R₀ t i I*Wslot i (I.absNorm/scales i)‖ ≤ Bf) →
      (∀i,∀Q∈H,Q.val∈R₀ i) →
      (∏i,2*scales i) ≤ Z^L → b*X₁*(∏i,2*scales i) ≤ Z^L →
      (∏i,scales i) ≤ Z^s →
      (∑i : rows,‖weightedSum
        (naturalCoefficients (χ i) S pool
          (fun j I=>slotCoefficient ν R₀ t j I*Wslot j (I.absNorm/scales j)) scales)
        (fun slot=>normalizedRow (χ i) (supportedRectangle S b X₁ X₂)
          (restrictedValue S (augmented S H (marked S slot)))
          (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) X₁ X₂)‖^2) ≤
        C*(sourceControl control Wlong)^2*(1+Height)^(2*n)*Z^(R+ε)*B^2 := by
  obtain ⟨n,control,C,hC,h00,hbound⟩ := ReferenceUniformRestricted.punctured_reference (α:=ι)
    ε L K a b xi Bf hε hL hK ha hb hxi hBf
  refine ⟨n,control,C,hC,h00,?_⟩
  intro Wlong hlong
  have hbound := hbound Wlong hlong
  intro Z R P s d l δ hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m D₀ rows χ hon hoff hrows hnonprincipal
    U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hUsharp hX₁ hX₂ hprod hshort
    hHeight ht₂ hmod hB hWs hWsm htest S H F hF hFcap hH hS henclose
    pool ν R₀ t Wslot scales hP hp hβ hHR hVcap hvolume hVsharp
  have hnonneg := ReferenceExtractionGeometry.mixed_exponents_nonneg
    R P s d l hR hs hd hl hcap
  have hslot : (∏i,2*scales i) ≤ (2:ℝ)^Fintype.card ι*Z^s := by
    rw [Finset.prod_mul_distrib]
    simpa only [Finset.prod_const,Finset.card_univ] using
      mul_le_mul_of_nonneg_left hVsharp (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
  have hc := short_reference_caps Z R P s d l δ xi b U X₁ X₂
    ((2:ℝ)^Fintype.card ι) (∏i,2*scales i)
    hZ hb (zero_le_one.trans hU) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    (Finset.prod_nonneg (fun i _=>by have := hP i;positivity))
    hX₁ hX₂ hprod hshort hUsharp hslot hfixed hξ
  exact hbound Z R (l+(R+d)/2+s+2*δ) (R+d+2*l-P+s+2*δ)
    hZ hR (by linarith [hnonneg.1]) (by linarith [hnonneg.2]) htotal hmax href
    η m D₀ rows χ hon hoff hrows hnonprincipal
    U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hX₁ hX₂ hHeight ht₂ hmod hB hWs hWsm htest
    S H F hF hFcap hH hS henclose pool
    (fun i I=>slotCoefficient ν R₀ t i I*Wslot i (I.absNorm/scales i)) scales
    hP hp hβ (canonical_hole_zero ν R₀ t H hHR Wslot scales)
    hVcap hvolume hc.1 hc.2


/-- Homogeneous uniform bound on the actual finite source rectangle.
The complete Rmask goes into ordinary holes and canonical slot zeros,
while the original character and its conductor remain unchanged. -/
theorem short_actual_reference (ε L K a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
    ∃ n : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ Wlong : 𝓢(ℝ,ℂ), Function.support (Wlong : ℝ → ℂ) ⊆ Icc a b →
      ∀ Z R P s d l δ : ℝ,
      1 ≤ Z → 0 ≤ R → 0 ≤ s → 0 ≤ d → 0 ≤ l → 0 ≤ δ → P+2*s+4*d < R →
      R+(l+(R+d)/2+s+2*δ) ≤ L →
      l+(R+d)/2+s+2*δ ≤ (4/5)*R → R+d+2*l-P+s+2*δ ≤ R/2 →
      (b+4)*b*(2:ℝ)^Fintype.card ι ≤ Z^δ → xi/2 ≤ δ →
      ∀ (η : Character) (m D₀ : O) (rows : Finset O) (χ : rows → Character),
      (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D₀ I*idealRowHom x.val I) →
      (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ i, (χ i).residue ≠ 1) →
      ∀ (U X₁ X₂ Height t₁ t₂ : ℝ) (Wshort : ℝ → ℂ) (B : ℝ),
      1 ≤ U → U ≤ Z^K → U ≤ Z^(R+d) → 0 < X₁ → 0 < X₂ → X₁*X₂ = Z^P → X₁ ≤ Z^l →
      0 ≤ Height → ‖t₂‖ ≤ Height → (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ U) →
      0 ≤ B → Function.support Wshort ⊆ Icc a b → ContDiff ℝ ∞ Wshort →
      (∀ (j : Fin 2) (x : ℝ), ‖scaleTest Wshort j x‖ ≤ B) →
      ∀ (S H : Finset PrimeIdeal) (Rmask F : Id), Rmask ≠ 0 → F ≠ 0 →
      ((F*Rmask).absNorm : ℝ) ≤ Z^K → (∀ Q ∈ H, Q.val ∣ F) →
      (∀ Q ∈ S, Supported Q.val ∧ (Q.val.absNorm : ℝ) ≤ Z^K) →
      (∀ I, Supported I → ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues S) →
      ∀ (pool : ι → Finset Id) (ν : ι → Character) (R₀ : ι → Finset Id)
        (t : ℝ) (Wslot : ι → ℝ → ℂ) (scales : ι → ℝ),
      (∀ i, pool i ⊆ primeValues S) → (∀ i I, I ∈ pool i → Prime I) →
      (∀ i, 0 < scales i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (I.absNorm : ℝ) ≤ 2*scales i) →
      (∀ i I, I ∈ pool i → ‖slotCoefficient ν R₀ t i I*Wslot i (I.absNorm/scales i)‖ ≤ Bf) →
      (∀ i Q, Q ∈ H → Q.val ∈ R₀ i) →
      (∏ i, 2*scales i) ≤ Z^L → b*X₁*(∏ i, 2*scales i) ≤ Z^L →
      (∏ i, scales i) ≤ Z^s →
      (∑ i : rows, ‖rectangleRow (χ i) S H Rmask pool (slotCoefficient ν R₀ t)
        Wslot scales (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) b X₁ X₂‖^2) ≤
        C*(sourceControl control Wlong)^2*(1+Height)^(2*n)*Z^(R+ε)*B^2 := by
  obtain ⟨n,control,C,hC,h00,hbound⟩ :=
    ReferenceUniformRestricted.short_punctured_reference (ι := ι) ε L K a b xi Bf
    hε hL hK ha hb hxi hBf
  refine ⟨n,control,C,hC,h00,?_⟩
  intro Wlong hlong
  have hbound := hbound Wlong hlong
  intro Z R P s d l δ hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m D₀ rows χ hon hoff hrows hnonprincipal
    U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hUsharp hX₁ hX₂ hprod hshort
    hHeight ht₂ hmod hB hWs hWsm htest S H Rmask F hRmask hF hFcap hH hS henclose
    pool ν R₀ t Wslot scales hpool hprime hP hp hβ hHR hVcap hvolume hVsharp
  have hnewH : ∀ Q ∈ enlargedHoles S H Rmask, Q.val ∣ F*Rmask := by
    intro Q hQ
    rcases (Finset.mem_filter.mp hQ).2 with hQ | hQ
    · exact (hH Q hQ).trans (dvd_mul_right F Rmask)
    · exact hQ.trans (dvd_mul_left Rmask F)
  have hnewHR : ∀ i Q, Q ∈ enlargedHoles S H Rmask → Q.val ∈ R₀ i ∪ primeSupport Rmask := by
    intro i Q hQ
    rcases (Finset.mem_filter.mp hQ).2 with hQ | hQ
    · exact Finset.mem_union_left _ (hHR i Q hQ)
    · exact Finset.mem_union_right _
        ((CenteredMomentNaturalPrimitive.prime_mem_support_iff Rmask Q.val hRmask Q.property).mpr hQ)
  have hnewβ : ∀ i I, I ∈ pool i →
      ‖slotCoefficient ν (fun j => R₀ j ∪ primeSupport Rmask) t i I *
        Wslot i (I.absNorm/scales i)‖ ≤ Bf := by
    intro i I hI
    have he := punctured_canonical_slot Rmask hRmask ν R₀ t i (⟨I,hprime i I hI⟩ : PrimeIdeal)
    rw [← he]
    unfold puncturedSlot
    split_ifs
    · exact hβ i I hI
    · simp only [zero_mul,norm_zero]
      exact zero_le_one.trans hBf
  have hh := hbound Z R P s d l δ hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m D₀ rows χ hon hoff hrows hnonprincipal
    U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hUsharp hX₁ hX₂ hprod hshort
    hHeight ht₂ hmod hB hWs hWsm htest S (enlargedHoles S H Rmask) (F*Rmask)
    (mul_ne_zero hF hRmask) hFcap hnewH hS henclose
    pool ν (fun i => R₀ i ∪ primeSupport Rmask) t Wslot scales hP hp hnewβ hnewHR
    hVcap hvolume hVsharp
  have hw₀ : Wshort 0 = 0 := by
    by_contra hn
    have hz := (hWs hn).1
    linarith
  have hphase₀ : phaseProfile Wshort t₁ 0 = 0 := by
    simp only [phaseProfile,hw₀,zero_mul]
  have hphase₁ : Function.support (phaseProfile Wshort t₁) ⊆ Iic b :=
    fun x hx => (hWs (phaseProfile_support Wshort t₁ hx)).2
  have hphase₂ : Function.support (phaseProfile Wlong t₂) ⊆ Iic b :=
    fun x hx => (hlong (phaseProfile_support Wlong t₂ hx)).2
  calc
    _ = ∑ i : rows, ‖puncturedRow (χ i) S (enlargedHoles S H Rmask) pool
        (fun j I => slotCoefficient ν (fun k => R₀ k ∪ primeSupport Rmask) t j I *
          Wslot j (I.absNorm/scales j)) scales
        (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) b X₁ X₂‖^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [rectangle_row_eq (χ i) S H Rmask hRmask pool hpool hprime ν R₀ t Wslot scales
        (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) hphase₀ b X₁ X₂ hX₁ hX₂
        hphase₁ hphase₂ (hoff i) henclose]
    _ ≤ _ := hh

end
end Candidate.Feedback.FourthPower.ReferenceUniformRestricted
