/- Copyright (c) 2026 Sil. Apache-2.0.
Finite-seminorm principal cancellation. The constants precede both
ordinary profiles and every actual physical row. The proved restricted
extraction is reused; normalization retains homogeneity in the profiles.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.PrincipalUniform
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.PrincipalPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.PrincipalQuantitative
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation CenteredMomentLattice
open CenteredMomentTwist
open CenteredMomentFiniteProfileExceptional CenteredMomentHeckeVolume ConcretePrimeRowBridge
open CanonicalRowCompletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelRowProfiles KernelRowPools KernelRowExpansion KernelMarkedRows KernelLabelledSlots
open KernelAssignmentReindex KernelPunctureRows PrincipalMarkedMass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- Bilinearity is used before norms, including when a control vanishes. -/
theorem normalized_row_scalars (χ : Character) (D : Finset IdealPair) (r : IdealPair→ℂ)
    (W₁ W₂ : ℝ→ℂ) (c₁ c₂ : ℂ) (X₁ X₂ : ℝ) :
    normalizedRow χ D r (fun x=>c₁*W₁ x) (fun x=>c₂*W₂ x) X₁ X₂=
      (c₁*c₂)*normalizedRow χ D r W₁ W₂ X₁ X₂ := by
  unfold normalizedRow pairProfile
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem norm_power_reconstruct (control : Finset (ℕ×ℕ)) (h00 : (0,0)∈control)
    (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (t : ℝ) :
    (normPowerProfile W a b ha hs (W.smooth ⊤) t:ℝ→ℂ)=
      fun x=>(sourceControl control W:ℂ)*
        normPowerProfile (normalizedProfile control W) a b ha
          ((normalizedProfile_support control W).trans hs)
          ((normalizedProfile control W).smooth ⊤) t x := by
  funext x
  have hr := congrArg (fun f : 𝓢(ℝ,ℂ)=>f x) (normalizedProfile_reconstruct control h00 W)
  change (sourceControl control W:ℂ)*normalizedProfile control W x=W x at hr
  simp only [normPowerProfile_apply]
  rw [←hr]
  ring

/-- Unit-seminorm version of the existing restricted rectangle argument.
The control family and constant are selected before the profiles. -/
theorem uniform_rectangle_unit (α B a b ε : ℝ) (hα : 0≤α) (hα4 : α<4/5)
    (hB : 0≤B) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧ ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      ∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      sourceControl control W₁≤1→sourceControl control W₂≤1→
      ∀Z : ℝ,1≤Z→∀F : Id,F≠0→(F.absNorm:ℝ)≤Z^B→
      ∀(S : Finset PrimeIdeal)(live : S→Bool),
      (∀P∈S,Supported P.val)→(∀P : S,live P=true→P.val.val∣F)→
      ∀η χ ψ : Character,(χ.modulus.absNorm:ℝ)≤Z^B→Q≤ψ.modulus→
      CenteredExceptionalProfile.InducedBy χ ψ→(∀I,¬Supported I→idealCoeff χ I=0)→
      ∀m A₀ z : O,goodLambda∣m→(2:O)∣m→
      (∀n,elementCoeff χ n=rowTwist (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)→
      ∀t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L : ℝ,0<L→
      L≤X₁→L≤X₂→L≤Y₁→L≤Y₂→X₁≤U₁→X₂≤U₂→Y₁≤U₁→Y₂≤U₂→
      X₁*X₂=T→Y₁*Y₂=T→
      (∀I,Supported I→((I.absNorm:ℝ)≤b*U₁∨(I.absNorm:ℝ)≤b*U₂)→primeSupport I⊆primeValues S)→
      ‖normalizedRow χ (supportedRectangle S b X₁ X₂) (restrictedValue S live)
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) X₁ X₂-
        normalizedRow χ (supportedRectangle S b Y₁ Y₂) (restrictedValue S live)
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) Y₁ Y₂‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖)^J*Real.sqrt T*L^(-α) := by
  obtain ⟨n,control,h00,hcontrol⟩ := volumeControl_source_control a b (ε/2) B ha (half_pos hε) hB
  obtain ⟨Cm,hCm,hmain⟩ := PrincipalRestricted.restricted_rectangle α B (ε/2) hα hα4 hB (half_pos hε)
  refine ⟨n,control,h00,?_⟩
  intro Q hQ
  obtain ⟨D,hD,hDcontrol⟩ := hcontrol Q
  let V := 128*(b+b)
  let A := 2*(128*b)*(128*b)
  let K := 1+8*D*V+A
  have hV : 0≤V := by dsimp [V];positivity
  have hA : 0≤A := by dsimp [A];positivity
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨Cm*K,mul_pos hCm hK,?_⟩
  intro W₁ W₂ hs₁ hs₂ hcontrol₁ hcontrol₂ Z hZ F hF hcut S live hS hlive
    η χ ψ hmod hQψ hind hχ m A₀ z hmLam hm2 hrow
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  let P₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let P₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  have hbound₁ (y : ℝ) : ‖P₁ y‖≤1 := by
    rw [show P₁ y=normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁ y from rfl,
      normPowerProfile_norm]
    exact (SchwartzMap.norm_le_seminorm ℝ W₁ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) h00).trans hcontrol₁)
  have hbound₂ (y : ℝ) : ‖P₂ y‖≤1 := by
    rw [show P₂ y=normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂ y from rfl,
      normPowerProfile_norm]
    exact (SchwartzMap.norm_le_seminorm ℝ W₂ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) h00).trans hcontrol₂)
  have hp₁ : Function.support (P₁:ℝ→ℂ)⊆Set.Icc a b :=
    (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
  have hp₂ : Function.support (P₂:ℝ→ℂ)⊆Set.Icc a b :=
    (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂
  let H := 1+‖t₁‖+‖t₂‖
  let E := Z^(ε/2)*H^n
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hE : 1≤E := by
    have hH : 1≤H^n := one_le_pow₀ (by
      change 1≤1+‖t₁‖+‖t₂‖
      exact (le_add_of_nonneg_right (norm_nonneg t₁)).trans
        (le_add_of_nonneg_right (norm_nonneg t₂)))
    simpa only [one_mul] using mul_le_mul (Real.one_le_rpow hZ (half_pos hε).le)
      hH (by norm_num : (0:ℝ)≤1) (Real.rpow_nonneg hZ0.le _)
  have herr (W : 𝓢(ℝ,ℂ)) (hs : Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
      (hc : sourceControl control W≤1) (t : ℝ) (ht : 1+‖t‖≤H) :
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t)≤D*E := by
    apply (hDcontrol W hs Z hZ χ hmod t).trans
    have hh := pow_le_pow_left₀ (by positivity : 0≤1+‖t‖) ht n
    calc
      _ ≤ D*1*Z^(ε/2)*H^n := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hD.le) (by positivity)
        · exact hh
        · positivity
        · positivity
      _ = D*E := by dsimp [E];ring
  have he₁ : volumeControl Q χ P₁≤D*E := herr W₁ hs₁ hcontrol₁ t₁
    (by dsimp only [H];exact le_add_of_nonneg_right (norm_nonneg t₂))
  have he₂ : volumeControl Q χ P₂≤D*E := herr W₂ hs₂ hcontrol₂ t₂
    (by dsimp only [H];linarith [norm_nonneg t₁])
  have hcoef : 4*(volumeControl Q χ P₁+volumeControl Q χ P₂)*V+A≤K*E := by
    have he := add_le_add he₁ he₂
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤4)) hV
    have hAE : A≤A*E := le_mul_of_one_le_right hA hE
    dsimp only [K]
    nlinarith
  have h := hmain Z hZ F hF hcut S live hS hlive η χ ψ Q hQ hQψ hind hχ
    m A₀ z hmLam hm2 hrow P₁ P₂ a b 1 1 ha hb zero_le_one zero_le_one
    hp₁ hp₂ (P₁.smooth ⊤) (P₂.smooth ⊤) hbound₁ hbound₂
    X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  dsimp only at h
  rw [PrincipalUniform.profile_zero P₁ a b ha hp₁,PrincipalUniform.profile_zero P₂ a b ha hp₂] at h
  simp only [mul_one] at h
  apply h.trans
  calc
    _ ≤ Cm*Z^(ε/2)*(K*E)*Real.sqrt T*L^(-α) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef (by positivity)) (Real.sqrt_nonneg _)) (by positivity)
    _ = (Cm*K)*(Z^(ε/2)*Z^(ε/2))*H^n*Real.sqrt T*L^(-α) := by dsimp [E];ring
    _ = _ := by rw [←Real.rpow_add hZ0,show ε/2+ε/2=ε by ring]

/-- Actual physical principal rows with homogeneous finite-seminorm
control. It applies to the inner K4 exceptional family after the exact
masked natural presentation; no fresh cubic divisor is assumed here.
The only fixed-inducing premise is the actual row predicate itself. -/
theorem uniform_physical (α B a b ε : ℝ) (hα : 0≤α) (hα4 : α<4/5)
    (hB : 0≤B) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧ ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      ∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀Z : ℝ,1≤Z→∀F : Id,F≠0→(F.absNorm:ℝ)≤Z^B→
      ∀S H : Finset PrimeIdeal,(∀P∈S,Supported P.val)→(∀P∈H,P.val∣F)→
      ∀(η : Character)(m A z : O),m≠0→A≠0→z≠0→goodLambda∣m→(2:O)∣m→
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B→
      CenteredExceptionalProfile.FixedInducingRow η Q m A z→
      ∀(ι : Type*) [Fintype ι],∀(pool : ι→Finset Id)(β : ι→Id→ℂ)(P M : ι→ℝ),
      (∀i,0<P i)→(∀i,0≤M i)→
      (∀i I,I∈pool i→Supported I∧(I.absNorm:ℝ)≤2*P i)→
      (∀i I,I∈pool i→‖β i I‖≤M i)→(∏i,2*P i)≤Z^B→
      ∀t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L : ℝ,0<L→
      L≤X₁→L≤X₂→L≤Y₁→L≤Y₂→X₁≤U₁→X₂≤U₂→Y₁≤U₁→Y₂≤U₂→
      X₁*X₂=T→Y₁*Y₂=T→
      (∀I,Supported I→((I.absNorm:ℝ)≤b*U₁∨(I.absNorm:ℝ)≤b*U₂)→primeSupport I⊆primeValues S)→
      ‖PrincipalPhysical.row η m A z S H pool β P
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) b X₁ X₂-
        PrincipalPhysical.row η m A z S H pool β P
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) b Y₁ Y₂‖≤
        C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
          (1+‖t₁‖+‖t₂‖)^J*(∏i,256*M i)*Real.sqrt (T*∏i,P i)*L^(-α) := by
  obtain ⟨n,control,h00,hrect⟩ := uniform_rectangle_unit α (2*B) a b ε
    hα hα4 (by positivity) ha hb hε
  refine ⟨n,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hrect Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ F hF hcut S H hS hH η m A z hm hA hz hmLam hm2 hcond hex
    ι instι pool β P M hP hM hp hβ hV
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  obtain ⟨χ,ψ,hmod,_,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A z
    hm hA hz hmLam hm2 hex
  have hm' : (χ.modulus.absNorm:ℝ)≤Z^B :=
    (show (χ.modulus.absNorm:ℝ)≤(HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)
      by exact_mod_cast hmod).trans hcond
  have hm2' : (χ.modulus.absNorm:ℝ)≤Z^(2*B) := hm'.trans
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  have hoff := PrincipalPhysical.character_off_supported η χ m A z hmLam hm2 hrow
  let N₁ := normalizedProfile control W₁
  let N₂ := normalizedProfile control W₂
  have hsN₁ : Function.support (N₁:ℝ→ℂ)⊆Set.Icc a b :=
    (normalizedProfile_support control W₁).trans hs₁
  have hsN₂ : Function.support (N₂:ℝ→ℂ)⊆Set.Icc a b :=
    (normalizedProfile_support control W₂).trans hs₂
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  let V₁n := normPowerProfile N₁ a b ha hsN₁ (N₁.smooth ⊤) t₁
  let V₂n := normPowerProfile N₂ a b ha hsN₂ (N₂.smooth ⊤) t₂
  let q := sourceControl control W₁*sourceControl control W₂
  have hq : 0≤q := mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  let G := fun slot : ι→S=>
    normalizedRow χ (supportedRectangle S b X₁ X₂) (restrictedValue S (augmented S H (marked S slot)))
      V₁ V₂ X₁ X₂-
    normalizedRow χ (supportedRectangle S b Y₁ Y₂) (restrictedValue S (augmented S H (marked S slot)))
      V₁ V₂ Y₁ Y₂
  let Gn := fun slot : ι→S=>
    normalizedRow χ (supportedRectangle S b X₁ X₂) (restrictedValue S (augmented S H (marked S slot)))
      V₁n V₂n X₁ X₂-
    normalizedRow χ (supportedRectangle S b Y₁ Y₂) (restrictedValue S (augmented S H (marked S slot)))
      V₁n V₂n Y₁ Y₂
  have hscale (slot : ι→S) : G slot=(q:ℂ)*Gn slot := by
    dsimp only [G,Gn,V₁,V₂,V₁n,V₂n,N₁,N₂]
    rw [norm_power_reconstruct control h00 W₁ a b ha hs₁ t₁,
      norm_power_reconstruct control h00 W₂ a b ha hs₂ t₂,
      normalized_row_scalars,normalized_row_scalars]
    simp only [q,Complex.ofReal_mul,mul_sub]
  let K := C*q*Z^ε*(1+‖t₁‖+‖t₂‖)^n*Real.sqrt T*L^(-α)
  have hK : 0≤K := by dsimp [K];positivity
  have hG (slot : ι→S) (_hi : Function.Injective slot)
      (hnz : (∏i,naturalCoefficients χ S pool β P i (slot i))≠0) : ‖G slot‖≤K := by
    have hpool := active_pool χ S pool β P slot hnz
    have hFslot := support_norm_bound F S slot P Z B hZ hcut
      (fun i=>(hp i _ (hpool i)).2) hV
    have h := hbound N₁ N₂ hsN₁ hsN₂ (normalizedProfile_control control W₁)
      (normalizedProfile_control control W₂) Z hZ
      (supportIdeal F S slot) (support_nonzero F hF S slot) hFslot
      S (augmented S H (marked S slot)) hS (support_divisor F S H slot hH)
      η χ ψ hm2' hQψ hind hoff m A z hmLam hm2 hrow
      t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
    rw [hscale slot,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq]
    exact (mul_le_mul_of_nonneg_left h hq).trans_eq (by dsimp [K];ring)
  rw [PrincipalPhysical.row_eq_character η χ m A z hrow,
    PrincipalPhysical.row_eq_character η χ m A z hrow,PrincipalMarked.row_difference]
  have hh := weighted_norm_le (naturalCoefficients χ S pool β P) G K hK hG
  apply hh.trans
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  calc
    _ ≤ K*∏i,(256*M i)*Real.sqrt (P i) := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun i _=>Finset.sum_nonneg (fun p _=>norm_nonneg _))
        (fun i _=>prime_slot_mass χ S (pool i) (β i) (P i) (M i) (hP i) (hM i) (hp i) (hβ i))) hK
    _ = _ := by
      rw [Finset.prod_mul_distrib,Real.sqrt_mul hT.le,Real.sqrt_prod _ (fun i _=>(hP i).le)]
      dsimp only [K,q]
      ring

end
end Candidate.FourthPower.PrincipalQuantitative
