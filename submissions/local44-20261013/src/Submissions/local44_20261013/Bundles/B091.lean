/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.local44_20261013.Bundles.B034
import Submissions.local44_20261013.Bundles.B047
import Submissions.local44_20261013.Bundles.B064
import Submissions.local44_20261013.Bundles.B065
import Submissions.local44_20261013.Bundles.B067
import Submissions.local44_20261013.Bundles.B069
import Submissions.local44_20261013.Bundles.B075
import Submissions.local44_20261013.Bundles.B077
import Submissions.local44_20261013.Bundles.B078
import Submissions.local44_20261013.Bundles.B081
import Submissions.local44_20261013.Bundles.B082
import Submissions.local44_20261013.Bundles.B083
import Submissions.local44_20261013.Bundles.B084
import Submissions.local44_20261013.Bundles.B085
import Submissions.local44_20261013.Bundles.B087
import Submissions.local44_20261013.Bundles.B089
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentTail ; sha256 ea1849041bde56d648e9967f8f3e6a38a3f37593e9da92f6bc589846b072ec97 -/
section



/-! Arbitrary saving for the literal common-coefficient discarded tail.
The fixed support factor precedes the live source; no allocated main
energy or assumed tail estimate is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceSecondZeroEnergy
open CenteredMomentExceptionalAmplitudePair CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_common_second_tail_arbitrary_saving (Csource B ξ saving : ℝ)
    (hB : 0 ≤ B) (hξ : 0 < ξ) :
    ∃ SΦ : Finset (ℕ×ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : Input ι) (R seed C L : Ideal O) (hC : Supported C)
      (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
      sourceRadius s ≤ Csource*volume s.toData → volume s.toData ≤ Z^B →
    ∀ (η : Character) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Tsec : ℝ),
      0 < K → Tsec ≤ Z^B → (volume s.toData/(C.absNorm : ℝ))^2/K ≤ Tsec →
      ‖secondDiscardedEnergy η t (commonSecondColumns (original s R seed) C hC)
        (commonSecondBeta (original s R seed) C L) Φ K Tsec Z ξ‖ / volume s.toData ≤
      Cbound*(originalAbsoluteProfile s B₁ B₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨Adec,hdecay⟩ := choose_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,D,hD,htail⟩ := second_discarded_energy_bound Adec
  let HN := Real.log (max 1 Csource)
  have hexp : Csource ≤ Real.exp HN := by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  refine ⟨SΦ,D*(Real.exp HN)^2*(1+Real.exp (2*HN))^2,by positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s R seed C L hC B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource hVcap η t Φ K Tsec hK hTcap hnom
  let V := volume s.toData
  let Eabs := originalAbsoluteProfile s B₁ B₂
  have hV : 0 < V := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
  have hNC : 0 < (C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hNC1 : (1 : ℝ) ≤ C.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hX : 0 < V/(C.absNorm : ℝ) := div_pos hV hNC
  have hXV : V/(C.absNorm : ℝ) ≤ V := div_le_self hV.le hNC1
  have hT : 0 < Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hnom
  have hmass : sourceAbsoluteMass (commonSecondColumns (original s R seed) C hC)
      (commonSecondBeta (original s R seed) C L) ≤ Eabs*V := by
    have hh := (common_second_absolute_mass (original s R seed) C L hC).trans
      (original_absolute_mass s R seed B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂)
    rwa [sourceAbsoluteMass_active] at hh
  have hN := commonSecond_source_norm_cap (original s R seed) C L hC (Real.exp HN*V)
    (fun I _ hI => (original_column_norm s R seed I hz₁ hz₂ hI).2.trans
      (hsource.trans (mul_le_mul_of_nonneg_right hexp hV.le)))
  have ht := htail η t (commonSecondColumns (original s R seed) C hC)
    (commonSecondBeta (original s R seed) C L) Φ K (V/(C.absNorm : ℝ)) HN Tsec Z 1 ξ
    hK hX hZ.1 le_rfl (by
      intro I hI hβ
      simpa only [mul_div_assoc] using hN I hI hβ) hnom (by simpa using hZ.2)
  have hnormsum : 0 ≤ sourceAbsoluteMass (commonSecondColumns (original s R seed) C hC)
      (commonSecondBeta (original s R seed) C L) := sourceAbsoluteMass_nonneg _ _
  have hE : 0 ≤ Eabs := by
    dsimp [Eabs,originalAbsoluteProfile]
    have hm : 0 ≤ ∏ j,s.M j := Finset.prod_nonneg (fun j _ => zero_le_one.trans (s.M_ge_one j))
    positivity
  have hdec := hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  have hmin : 0 < min 1 (kernelReference Tsec HN) := lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have hden : 0 < (min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec := by positivity
  calc
    _ ≤ ((Eabs*V)^2*K*(Real.exp HN*V)^2*(D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V := by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      change (sourceAbsoluteMass _ _)^2 * _ * _ * _ / _ ≤ _
      gcongr
    _ = (D*(Real.exp HN)^2*Eabs^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹) := by
      field_simp [ne_of_gt hV,ne_of_gt hmin]
    _ ≤ (D*(Real.exp HN)^2*Eabs^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)) :=
      mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = _ := by ring


theorem tail_prime_projector_absorption
    (Z B saving K P NL F value : ℝ)
    (hZ : 1 ≤ Z) (hK : 0 ≤ K) (hP : 1 ≤ P) (hNL : 0 < NL) (hF : 0 ≤ F)
    (hKcap : K ≤ Z^B) (hNLcap : NL ≤ Z^B)
    (hvalue : value ≤ F*K*Z^(-(saving+2*B))) :
    value/P ≤ F*Z^(-saving)/NL := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hp : 0 < P := zero_lt_one.trans_le hP
  have hpow := mul_le_mul hKcap hNLcap hNL.le (Real.rpow_nonneg hz.le B)
  have hkn : K*NL ≤ Z^(2*B) := by
    simpa only [←Real.rpow_add hz,show B+B = 2*B by ring] using hpow
  apply (div_le_iff₀ hp).mpr
  apply le_trans hvalue
  have hscaled : F*K*Z^(-(saving+2*B)) ≤ F*Z^(-saving)/NL := by
    apply (le_div_iff₀ hNL).mpr
    calc
      _ = F*(K*NL)*Z^(-(saving+2*B)) := by ring
      _ ≤ F*Z^(2*B)*Z^(-(saving+2*B)) := by gcongr
      _ = _ := by rw [mul_assoc,←Real.rpow_add hz];congr 2;ring
  exact hscaled.trans (le_mul_of_one_le_right (by positivity) hP)

theorem actual_common_second_tail_normalized (Csource B ξ saving : ℝ)
    (hB : 0 ≤ B) (hξ : 0 < ξ) :
    ∃ SΦ : Finset (ℕ×ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : Input ι) (R seed C L : Ideal O) (hC : Supported C), L ≠ 0 →
    ∀ (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
      sourceRadius s ≤ Csource*volume s.toData → volume s.toData ≤ Z^B →
      (L.absNorm : ℝ) ≤ Z^B →
    ∀ (η : Character) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Tsec P : ℝ),
      0 < K → K ≤ Z^B → 1 ≤ P → Tsec ≤ Z^B →
      (volume s.toData/(C.absNorm : ℝ))^2/K ≤ Tsec →
      ‖secondDiscardedEnergy η t (commonSecondColumns (original s R seed) C hC)
        (commonSecondBeta (original s R seed) C L) Φ K Tsec Z ξ‖ / (volume s.toData*P) ≤
      (Cbound*(originalAbsoluteProfile s B₁ B₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*Z^(-saving)/(L.absNorm : ℝ) := by
  obtain ⟨SΦ,Cbound,hCbound,hh⟩ := actual_common_second_tail_arbitrary_saving (ι := ι)
    Csource B ξ (saving+2*B) hB hξ
  refine ⟨SΦ,Cbound,hCbound,?_⟩
  filter_upwards [hh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s R seed C L hC hL B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource hVcap hLcap
    η t Φ K Tsec P hK hKcap hP hTcap hnom
  have hNL : 0 < (L.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL)
  have hb := hZ.2 s R seed C L hC B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource hVcap
    η t Φ K Tsec hK hTcap hnom
  rw [←div_div]
  exact tail_prime_projector_absorption Z B saving K P (L.absNorm : ℝ)
    _ _ hZ.1.le hK.le hP hNL (by positivity) hKcap hLcap hb

#print axioms actual_common_second_tail_normalized
#print axioms actual_common_second_tail_arbitrary_saving
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentTail -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentZeroNormalized ; sha256 ea48a3f7cdd1c802ce20ff689fef7c7b9f567f54ecc3b070c9265ae2722a24b9 -/
section


/-! The actual coherent zero term, including the Poisson multiplier and
one prime average, has a strict 87/1000 reserve and keeps 1/NL. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceSecondZeroEnergy
open CenteredMomentExceptionalAmplitudePair EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem coherent_zero_scalar_power
    (Z A c d R E M omega primeLoss K P C : ℝ)
    (hZ : 1 ≤ Z) (hc : 0 ≤ c) (hd : 0 ≤ d) (hA : A ≤ 883/1000) (hM : 1 ≤ M)
    (hK : 0 ≤ K) (hP : 0 < P) (hC : 0 < C)
    (hKcap : K ≤ Z^(2*A-c-d+R+E-M+max (d-c) 0+6*(3/500)+omega))
    (hprime : 1/P ≤ Z^(-(3/500)+primeLoss)) (hcommon : Z^c ≤ C) :
    K/(C*P) ≤ Z^(A-2*c+R+E-87/1000+omega+primeLoss) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hi : 1/C ≤ Z^(-c) := by
    rw [Real.rpow_neg hz.le]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hz _) hcommon
  have hmax : max (d-c) 0 ≤ d := max_le (by linarith) hd
  calc
    _ = K*(1/C)*(1/P) := by ring
    _ ≤ Z^(2*A-c-d+R+E-M+max (d-c) 0+6*(3/500)+omega)*Z^(-c)*Z^(-(3/500)+primeLoss) :=
      mul_le_mul (mul_le_mul hKcap hi (by positivity) (by positivity)) hprime
        (by positivity) (by positivity)
    _ = Z^((2*A-c-d+R+E-M+max (d-c) 0+6*(3/500)+omega)+(-c)+(-(3/500)+primeLoss)) := by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem actual_common_second_zero_normalized (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ (Z : ℝ), 1 ≤ Z →
      ∀ (s : Input ι) (R seed C L : Ideal O) (hC : Supported C) (hL : L ≠ 0)
        (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
      0 ≤ sourceRadius s → sourceRadius s ≤ Z^B →
      ∀ (η : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ))
        (A c d Rwidth E M omega primeLoss K P : ℝ),
      0 ≤ c → 0 ≤ d → A ≤ 883/1000 → 1 ≤ M → 0 ≤ K → 0 < P →
      K ≤ Z^(2*A-c-d+Rwidth+E-M+max (d-c) 0+6*(3/500)+omega) →
      1/P ≤ Z^(-(3/500)+primeLoss) → Z^c ≤ (C.absNorm : ℝ) →
      ‖((K : ℂ)*paperRadialFourier W 0)*
        sourceSecondZero (commonSecondColumns (original s R seed) C hC)
          (commonSecondBeta (original s R seed) C L) η t‖ /
        (volume s.toData*P) ≤
      (Cbound*(2*B₁*B₂*∏ j,s.M j)^2*|(∏ j,s.hi j)*s.b₁*s.b₂| *
        ‖paperRadialFourier W 0‖)*
        Z^(A-2*c+Rwidth+E-87/1000+omega+primeLoss+ε)/(L.absNorm : ℝ) := by
  obtain ⟨D,hD,hd⟩ := actual_common_second_zero (ι := ι) B ε hB hε
  refine ⟨D,hD,?_⟩
  intro Z hZ s R seed C L hC hL B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource₀ hsource
    η t W A c d Rwidth E M omega primeLoss K P hc hd' hA hM hK hP hKcap hprime hcommon
  have hv : 0 < volume s.toData := volume_pos s.toData
  have hnC : 0 < (C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hnL : 0 < (L.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL)
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hsr : sourceRadius s = ((∏ j,s.hi j)*s.b₁*s.b₂)*volume s.toData := by
    unfold sourceRadius CenteredMomentExceptionalAmplitudePair.volume
    ring
  have hsrle : sourceRadius s ≤ |(∏ j,s.hi j)*s.b₁*s.b₂| *volume s.toData := by
    rw [hsr]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hv.le
  have hzbound := hd Z hZ s R seed C L hC hL B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂
    hsource₀ hsource η t
  have hscalar := coherent_zero_scalar_power Z A c d Rwidth E M omega primeLoss K P
    (C.absNorm : ℝ) hZ hc hd' hA hM hK hP hnC hKcap hprime hcommon
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hK]
  calc
    _ ≤ K*‖paperRadialFourier W 0‖*
      (D*(2*B₁*B₂*∏ j,s.M j)^2*Z^ε*(|(∏ j,s.hi j)*s.b₁*s.b₂| *volume s.toData)/
        ((C.absNorm : ℝ)*(L.absNorm : ℝ)))/(volume s.toData*P) := by
      gcongr
      exact hzbound.trans (by gcongr)
    _ = (D*(2*B₁*B₂*∏ j,s.M j)^2*|(∏ j,s.hi j)*s.b₁*s.b₂| *‖paperRadialFourier W 0‖)*
        (K/((C.absNorm : ℝ)*P))*Z^ε/(L.absNorm : ℝ) := by field_simp [ne_of_gt hv] <;> ring
    _ ≤ (D*(2*B₁*B₂*∏ j,s.M j)^2*|(∏ j,s.hi j)*s.b₁*s.b₂| *‖paperRadialFourier W 0‖)*
        Z^(A-2*c+Rwidth+E-87/1000+omega+primeLoss)*Z^ε/(L.absNorm : ℝ) := by gcongr
    _ = _ := by rw [mul_assoc,←Real.rpow_add hz]

#print axioms coherent_zero_scalar_power
#print axioms actual_common_second_zero_normalized
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentZeroNormalized -/

/- BEGIN ORIGINAL MODULE Analytic.JointDirectCommonAmplification ; sha256 7303e46f94d6cf29123b11d2845a620118f4ce1879e8d9ee6c4115137202d12c -/
section



/-! Direct common-source amplification. The original common Gaussian main
term survives intact; only its three genuine extraction errors are allocated. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentGaussEnergy CenteredMomentGaussNormalization
open CenteredMomentAmplificationEnergy CenteredMomentAmplificationEligibility
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentFirstScale
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentFirstAnnularGeometry
open CenteredMomentHeckeColumnWindow CenteredMomentFirstAnnularInput
open CenteredMomentChildRows CenteredMomentFirstAllocationGaussEnergy RayFourExpansion
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance directCommonAmplificationDecEq : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma errorEnergy_central {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (T : ℝ) (hT : 0 < T) (h p : O) :
    errorEnergy S a ha (fun i => (Real.sqrt T:ℂ)⁻¹*c i) h p =
      errorEnergy S a ha c h p / T := by
  rw [errorEnergy_const_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt hT.le]
  ring

/-- All characters are chosen before the input, first allocation, and
height. The main term is the original common energy, with no first
allocation count; the error is exactly `allocatedExtractedErrors`. -/
theorem eventually_direct_common_annular_amplification
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (N : ℕ) (a b sigma loss BR Bs Mmax eta Csec xi reserve : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hsigma : 0 < sigma) (hloss : 0 < loss)
    (hM : 0 ≤ Mmax) (hgap : eta < sigma/6) (hCsec : 1 ≤ Csec)
    (hxi : 0 ≤ xi) (hreserve : 0 < reserve) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss) ≤ (P.card : ℝ) ∧
      ∃ τ : (J : Finset ι) → Character → elementPool P → Fin 3 → RayCharacter → Character,
        (∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (s : Input ι), Fintype.card ι ≤ N → a ≤ s.lower → s.upper ≤ b →
        ∀ (C R seed L : Ideal O) (hC : Supported C), seed ∣ C →
        ∀ (parent : Character) (t : ℝ) (z : ι → ℝ),
        (∀ j, z j ≤ eta) → (∀ j, s.P j = Z^(z j)) →
        R ≠ 0 → L ≠ 0 → ((R*C).absNorm : ℝ) ≤ Z^BR → (L.absNorm : ℝ) ≤ Z^Bs →
        ∀ (I J E : Ideal O), E ≠ 0 → ∀ (K X Tsec H₀ d c : ℝ),
        0 < K → 0 < X → Tsec ≤ Csec*firstNominalScale I J E K X →
        0 < H₀ → H₀ ≤ 4*frequencyRadius Tsec Z xi → 8*H₀ ≤ Z^Mmax →
        (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC parent t L
          CenteredMomentFirstAnnularMajorant.profile H₀).re / volume s ≤
          (56/(P.card : ℝ))*((Mmax+2*sigma)/(sigma/6))*
            ((CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC parent t L ballProfile
              (mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
                (frequencyLoss Z (32*Csec) xi) reserve)).re / volume s) +
          allocatedExtractedErrors N s C R L parent t b Z d (nominalLog I J E K X Z) c sigma
            (frequencyLoss Z (32*Csec) xi) reserve P (fun B => τ (liveIndices B.val) parent) := by
  filter_upwards [eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
    hsigma hloss hM hgap,eventually_support_reserve reserve hreserve] with Z hsource hsupp
  obtain ⟨hZ,hP,hcard,hsep,hdata,hamp⟩ := hsource
  let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
  let delta := frequencyLoss Z (32*Csec) xi
  have hdelta : 0 ≤ delta := frequencyLoss_nonneg Z (32*Csec) xi hZ (by linarith) hxi
  have hf (J : Finset ι) := exists_input_common_error_families (ι := J) P
    (fun Q hQ => (hdata Q hQ).1) (fun Q hQ => (hdata Q hQ).2.1)
    Z sigma b eta delta reserve hZ hsigma.le hb hsep
    (fun Q hQ => (hdata Q hQ).2.2.1) hdelta hsupp.2
  choose τ hτ herr using hf
  refine ⟨hZ,hP,hcard,τ,hτ,?_⟩
  intro s hn hlo hhi C R seed L hC hseed parent t z hz hlen hR hL hRCcap hLcap
    I J E hE K X Tsec H₀ d c hK hX hsec hH₀ houter hcap
  let Q := residualPool C hC.1 (original s R seed).columns
  let coeff : supportedColumns Q → ℂ := fun q =>
    (if IsCoprime C (q : Ideal O) ∧ L ∣ (q : Ideal O) then (original s R seed).beta (C*q) else 0)*
      heightCoeff parent t q
  let coeffN : supportedColumns Q → ℂ := fun q => (Real.sqrt (volume s):ℂ)⁻¹*coeff q
  let K₀ := nominalLog I J E K X Z
  let Main := (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC parent t L ballProfile
    (mainCommonRadius Z d K₀ c sigma delta reserve)).re / volume s
  let A := (max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)
  let Err := A*∑ B : actualAllocations s.pools C,
    if frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 then
      (frozenControl B.val s.M)^2*∑ p : elementPool P,
        firstExtractedErrors (child s C R B parent t) (R*C) L Z d K₀ c sigma delta reserve p
          (τ (liveIndices B.val) parent p) else 0
  have hsec' : 32*Tsec ≤ (32*Csec)*firstNominalScale I J E K X := by nlinarith
  have hfreq : 8*H₀ ≤ frequencyRadius (32*Tsec) Z xi := by
    unfold frequencyRadius at houter ⊢
    nlinarith
  have hdyad (j : ℤ) (hj : j ∈ CenteredMomentFirstAnnularMajorant.bands H₀) :
      (∑' h : O,dyadicWeight j (normValue h)*
        ‖gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) coeffN h‖^2) ≤
      (8/(P.card:ℝ))*(((Mmax+2*sigma)/(sigma/6))*Main+Err) := by
    have henclose : Real.logb Z (dyadicScale j) ≤ K₀+delta :=
      retained_nominal_upper I J E hE K X Z (32*Csec) (32*Tsec) xi hK hX hZ
        (by linarith) hsec' j (bands_retained H₀ _ hH₀ hfreq j hj)
    have herrB (B : actualAllocations s.pools C) :
        (∑ p ∈ elementPool P, ∑ h ∈ (dyadRows j).filter (fun h => eligible (R*C) L h p),
          errorEnergy Finset.univ
            (sourceGenerator (original (child s C R B parent t) (R*C) L).columns)
            (sourceGenerator_supported (original (child s C R B parent t) (R*C) L).columns)
            ((original (child s C R B parent t) (R*C) L).coefficient parent fixedBadMask t
              (volume (child s C R B parent t))) h p) ≤
          ∑ p : elementPool P,
            firstExtractedErrors (child s C R B parent t) (R*C) L Z d K₀ c sigma delta reserve p
              (τ (liveIndices B.val) parent p) := by
      exact herr (liveIndices B.val) (child s C R B parent t)
        (fun i y hy => ((s.slot_support i.val hy).2.trans hhi))
        (fun i => z i.val) (fun i => hz i.val) (fun i => hlen i.val)
        (R*C) L d K₀ c j henclose
    have herrors : (∑ p ∈ elementPool P,
        ∑ h ∈ (dyadRows j).filter (fun h => eligible (R*C) L h p),
          errorEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) coeffN h p) ≤ Err := by
      let EE := fun (B : actualAllocations s.pools C) (p h : O) =>
        errorEnergy Finset.univ
          (sourceGenerator (original (child s C R B parent t) (R*C) L).columns)
          (sourceGenerator_supported (original (child s C R B parent t) (R*C) L).columns)
          ((original (child s C R B parent t) (R*C) L).coefficient parent fixedBadMask t
            (volume (child s C R B parent t))) h p
      calc
        _ ≤ ∑ p ∈ elementPool P,
            ∑ h ∈ (dyadRows j).filter (fun h => eligible (R*C) L h p),
              A*∑ B : actualAllocations s.pools C,
                if frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 then
                  (frozenControl B.val s.M)^2*EE B p h else 0 := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro h hh
          change errorEnergy _ _ _ (fun q => (Real.sqrt (volume s):ℂ)⁻¹*coeff q) h p ≤ _
          rw [errorEnergy_central _ _ _ _ _ (volume_pos s)]
          exact common_errorEnergy_allocated_inputs N a b ha s hn hlo hhi C R seed hC hseed parent t L h p
        _ = A*∑ B : actualAllocations s.pools C,
              if frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 then
                (frozenControl B.val s.M)^2*
                  (∑ p ∈ elementPool P, ∑ h ∈ (dyadRows j).filter (fun h => eligible (R*C) L h p), EE B p h)
              else 0 := by
          simp_rw [←Finset.mul_sum]
          congr 1
          calc
            _ = ∑ p ∈ elementPool P, ∑ B : actualAllocations s.pools C,
                  ∑ h ∈ (dyadRows j).filter (fun h => eligible (R*C) L h p),
                    if frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 then
                      (frozenControl B.val s.M)^2*EE B p h else 0 := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [Finset.sum_comm]
            _ = _ := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro B _
              simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,←Finset.mul_sum]
        _ ≤ Err := by
          apply mul_le_mul_of_nonneg_left _ (by dsimp [A]; positivity)
          apply Finset.sum_le_sum
          intro B _
          split_ifs with hB
          · exact mul_le_mul_of_nonneg_left (herrB B) (sq_nonneg _)
          · exact le_rfl
    have hh := hamp Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) coeffN
      (R*C) L (mul_ne_zero hR hC.1) hL hRCcap hLcap j
      (bands_log_cap H₀ Z Mmax hH₀ hZ hcap j hj) (d+K₀-Real.logb Z (dyadicScale j)) c
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ herrors
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hm := main_energy_common Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      coeffN Z d K₀ (Real.logb Z (dyadicScale j)) c sigma delta reserve hZ hdelta henclose hsupp.2
    apply hm.trans_eq
    exact gaussEnergy_central _ _ _ coeff _ (volume_pos s) _ _
  have hh := common_bound_auto Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    coeffN H₀ _ hH₀ hdyad
  rw [gaussEnergy_central _ _ _ coeff _ (volume_pos s)] at hh
  apply hh.trans_eq
  change 7*((8/(P.card:ℝ))*(((Mmax+2*sigma)/(sigma/6))*Main+Err)) = _
  unfold allocatedExtractedErrors
  dsimp only [Err]
  simp only [mul_add]
  congr 1
  · change 7*(8/(P.card:ℝ)*((Mmax+2*sigma)/(sigma/6)*Main)) = _
    dsimp only [Main,K₀,delta]
    ring
  · dsimp only [A,K₀,delta,P]
    simp only [Finset.mul_sum,mul_ite,mul_zero]
    apply Finset.sum_congr rfl
    intro B _
    split_ifs
    · apply Finset.sum_congr rfl
      intro p _
      ring
    · rfl

#print axioms eventually_direct_common_annular_amplification
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointDirectCommonAmplification -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstCoarseLabels ; sha256 116b47cc3d0038a9520dd8c7966ee3c446e14a26f374f7af3a30002a3e2d7221 -/
section



/-! Exact comparison of the first Fourier coarse sums with the literal
projector sum; both finite ray labels contribute a fixed constant. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstDivisorCommonBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

namespace FirstJointLabel
variable {ι : Type*} [Fintype ι]

lemma sourceIndex_projector_sum (s : FirstJointLabel ι) (f : Ideal O → ℝ) :
    (∑ i : s.SourceIndex, f i.1) =
      (Fintype.card RayCharacter : ℝ)^2*(∑ L ∈ s.projectors, f L) := by
  simp only [SourceIndex,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_prod,Nat.cast_mul]
  rw [Finset.sum_coe_sort s.projectors (fun L =>
    ((Fintype.card RayCharacter : ℝ)*(Fintype.card RayCharacter : ℝ))*f L)]
  simp only [←Finset.mul_sum]
  ring

lemma source_leftCoarse_sum (s : FirstJointLabel ι) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ i : s.SourceIndex, (s.sourceChild i).leftCoarse W K) =
      (Fintype.card RayCharacter : ℝ)^2*
        (∑ L ∈ s.projectors, coarse s.data s.C s.hC L W K) :=
  s.sourceIndex_projector_sum (fun L => coarse s.data s.C s.hC L W K)

lemma source_rightCoarse_sum (s : FirstJointLabel ι) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ i : s.SourceIndex, (s.sourceChild i).rightCoarse W K) =
      (Fintype.card RayCharacter : ℝ)^2*
        (∑ L ∈ s.projectors, coarse s.data s.D s.hD L W K) :=
  s.sourceIndex_projector_sum (fun L => coarse s.data s.D s.hD L W K)

end FirstJointLabel

theorem first_source_coarse_powers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (F U b₁ b₂ B₁ B₂ D : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hD : 0 ≤ D)
    (s : Input ι) (R seed : Ideal O) (q : FirstJointLabel ι)
    (hdata : q.data = original s R seed)
    (W : 𝓢(ℝ,ℂ)) (K Z A B J : ℝ) (hZ : 1 ≤ Z) (hJ : 0 ≤ J)
    (hN : Fintype.card ι ≤ N) (hF : ∀ i, s.M i ≤ F)
    (hU : s.upper ≤ U) (hb₁ : s.b₁ ≤ b₁) (hb₂ : s.b₂ ≤ b₂)
    (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (hbound₁ : ∀ x, ‖s.W₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖s.W₂ x‖ ≤ B₂)
    (hK : 0 < K) (hKcap : K ≤ Z^J) (hW : QuadraticInitialBound.diagonalControl W ≤ D)
    (hsource : sourceRadius s ≤ Z^B) (hvolume : volume s.toData ≤ Z^A) :
    (∑ i : q.SourceIndex, (q.sourceChild i).leftCoarse W K) ≤
      (volume s.toData/(q.C.absNorm : ℝ))*
        (((Fintype.card RayCharacter : ℝ)^2*128*D*
          (firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2)*Z^(J+2*B+A)) ∧
    (∑ i : q.SourceIndex, (q.sourceChild i).rightCoarse W K) ≤
      (volume s.toData/(q.D.absNorm : ℝ))*
        (((Fintype.card RayCharacter : ℝ)^2*128*D*
          (firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2)*Z^(J+2*B+A)) := by
  have hh (C : Ideal O) (hC : Supported C) :=
    original_common_coarse_projector_power N F U b₁ b₂ B₁ B₂ D hB₁ hB₂ hD
      s R seed C hC q.projectors (fun _ => W) (fun _ => K) Z A B J hZ hJ
      hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ (fun _ _ => hK)
      (fun _ _ => hKcap) (fun _ _ => hW) hsource hvolume
  constructor
  · rw [q.source_leftCoarse_sum,hdata]
    exact (mul_le_mul_of_nonneg_left (hh q.C q.hC) (sq_nonneg _)).trans_eq (by ring)
  · rw [q.source_rightCoarse_sum,hdata]
    exact (mul_le_mul_of_nonneg_left (hh q.D q.hD) (sq_nonneg _)).trans_eq (by ring)

#print axioms first_source_coarse_powers

/-- A literal `firstSourceLabels` bound. The only cardinal hypothesis is
on outer arithmetic/dyadic labels; the projector pool is handled from
the nonzero source columns inside `first_source_coarse_powers`. -/
theorem first_source_joint_coarse_powers {ι Λ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Λ]
    (N : ℕ) (F U b₁ b₂ B₁ B₂ D : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hD : 0 ≤ D)
    (s : Input ι) (R seed : Ideal O) (labels : Finset Λ) (q : Λ → FirstJointLabel ι)
    (hdata : ∀ l ∈ labels, (q l).data = original s R seed)
    (W : Λ → 𝓢(ℝ,ℂ)) (K : Λ → ℝ) (Z A B J G Q NC ND : ℝ)
    (hZ : 1 ≤ Z) (hJ : 0 ≤ J) (hNC : 0 < NC) (hND : 0 < ND)
    (hNCcap : NC ≤ Z^Q) (hNDcap : ND ≤ Z^Q) (hcard : (labels.card : ℝ) ≤ Z^G)
    (hN : Fintype.card ι ≤ N) (hF : ∀ i, s.M i ≤ F)
    (hU : s.upper ≤ U) (hb₁ : s.b₁ ≤ b₁) (hb₂ : s.b₂ ≤ b₂)
    (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (hbound₁ : ∀ x, ‖s.W₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖s.W₂ x‖ ≤ B₂)
    (hK : ∀ l ∈ labels, 0 < K l) (hKcap : ∀ l ∈ labels, K l ≤ Z^J)
    (hW : ∀ l ∈ labels, QuadraticInitialBound.diagonalControl (W l) ≤ D)
    (hsource : sourceRadius s ≤ Z^B) (hvolume : volume s.toData ≤ Z^A) :
    (∑ k ∈ firstSourceLabels labels q,
      ((q k.1).sourceChild k.2).leftCoarse (W k.1) (K k.1)) ≤
      (volume s.toData/NC)*
        (((Fintype.card RayCharacter : ℝ)^2*128*D*
          (firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2)*Z^(J+2*B+A+G+Q)) ∧
    (∑ k ∈ firstSourceLabels labels q,
      ((q k.1).sourceChild k.2).rightCoarse (W k.1) (K k.1)) ≤
      (volume s.toData/ND)*
        (((Fintype.card RayCharacter : ℝ)^2*128*D*
          (firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2)*Z^(J+2*B+A+G+Q)) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hv := CenteredMomentSourceInputTailUniform.volume_pos s
  let P := (Fintype.card RayCharacter : ℝ)^2*128*D*
    (firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hh (l) (hl : l ∈ labels) := first_source_coarse_powers N F U b₁ b₂ B₁ B₂ D
    hB₁ hB₂ hD s R seed (q l) (hdata l hl) (W l) (K l) Z A B J hZ hJ
    hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ (hK l hl) (hKcap l hl) (hW l hl) hsource hvolume
  have hnorm (I : Ideal O) (hI : I ≠ 0) : (1:ℝ) ≤ I.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hsum (e : Λ → ℝ) (ref : ℝ) (href : 0 < ref) (hrefcap : ref ≤ Z^Q)
      (he : ∀ l ∈ labels, e l ≤ volume s.toData*(P*Z^(J+2*B+A))) :
      (∑ l ∈ labels, e l) ≤ (volume s.toData/ref)*(P*Z^(J+2*B+A+G+Q)) := by
    calc
      _ ≤ (labels.card : ℝ)*(volume s.toData*(P*Z^(J+2*B+A))) := by
        simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum he
      _ ≤ Z^G*(volume s.toData*(P*Z^(J+2*B+A))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (volume s.toData/ref)*(P*Z^(J+2*B+A+G))*ref := by
        simp only [Real.rpow_add hz]
        field_simp [href.ne']
      _ ≤ (volume s.toData/ref)*(P*Z^(J+2*B+A+G))*Z^Q :=
        mul_le_mul_of_nonneg_left hrefcap (by positivity)
      _ = _ := by simp only [Real.rpow_add hz]; ring
  constructor
  · simp only [firstSourceLabels,Finset.sum_sigma]
    apply hsum _ NC hNC hNCcap
    intro l hl
    exact (hh l hl).1.trans (mul_le_mul_of_nonneg_right
      (div_le_self hv.le (hnorm _ (q l).hC.1)) (by positivity))
  · simp only [firstSourceLabels,Finset.sum_sigma]
    apply hsum _ ND hND hNDcap
    intro l hl
    exact (hh l hl).2.trans (mul_le_mul_of_nonneg_right
      (div_le_self hv.le (hnorm _ (q l).hD.1)) (by positivity))

#print axioms first_source_joint_coarse_powers
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstCoarseLabels -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighKernelGeometry ; sha256 fb7e00a02817d2f88bb0fbda1deb1a0627954d41a2e66ddc660e85a99afe5074 -/
section







/-! The high retained source estimate with every buffered product
constructed internally from its literal source coefficient identities. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization HeckeDetectorDyadicGeometry
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (η : Character) (η₀ : Slot → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

theorem actual_joint_high_kernel_from_geometry
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (ηcommon : Character) (hanchor : ∀ j, η₀ j = ηcommon)
    (Wslot : ℝ → ℂ) (hVslot : ∀ j, V j = Wslot)
    (bslot : ℝ) (hBslot : ∀ j, Bprofile j = bslot)
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 < ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (τdetector dmin heightLoss : ℝ) (I : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin) (hheightLoss : 0 < heightLoss)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss)
    (Wkernel : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (tailA targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), dmin ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel)
        (w : JointReconstructionLabel → NonzeroElement),
      (∀ v ∈ S, (w v).val = v.row (unit v)) →
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧ primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (s : JointReconstructionLabel → CommonSecondKernelLabel Slot)
        (Ds : JointReconstructionLabel → Finset (Ideal O))
        (z : JointReconstructionLabel → O) (t K Radius tbase firstU firstTheta : JointReconstructionLabel → ℝ)
        (n : JointReconstructionLabel → Fin 4 → ℤ) (rayWeight : JointReconstructionLabel → ℂ)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ)
        (aSource : ℝ), 0 < aSource →
      (∀ v ∈ S, ‖rayWeight v‖ ≤ 1) →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < dyadicScale (n v 2) ∧ 0 < dyadicScale (n v 3) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ dyadicScale (n v 2) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ dyadicScale (n v 3)) →
      ∀ (parentL parentR : JointReconstructionLabel → JointParentLabel η)
        (NL : ∀ v, CenteredMomentNaturalRowSource.NaturalRow (parentL v).val (w v).val)
        (NR : ∀ v, CenteredMomentNaturalRowSource.NaturalRow (parentR v).val (w v).val)
        (punctureL punctureR : JointReconstructionLabel → Ideal O),
      (∀ v, punctureL v ≠ 0) → (∀ v, punctureR v ≠ 0) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, ∀ height : ℝ, ∀ J : Ideal O, CenteredMomentHeckeExpansion.rowWeight
        (CenteredMomentChildRows.childCharacter (s v).parent (s v).leftRay)
        (fixedBadMask*idealGenerator ((s v).puncture*((s v).firstCommon*(s v).second.val.1)))
        (s v).toKernelLabel.frequency (z v) height J =
        CenteredMomentHeckeExpansion.rowWeight (parentL v).val
          (fixedBadMask*idealGenerator (punctureL v)) 1 (w v).val height J) →
      (∀ v ∈ S, ∀ height : ℝ, ∀ J : Ideal O, CenteredMomentHeckeExpansion.rowWeight
        (CenteredMomentChildRows.childCharacter (s v).parent ((s v).rightRay⁻¹))
        (fixedBadMask*idealGenerator ((s v).puncture*((s v).firstCommon*(s v).second.val.2)))
        (s v).toKernelLabel.frequency (-(z v)) height J =
        CenteredMomentHeckeExpansion.rowWeight (parentR v).val
          (fixedBadMask*idealGenerator (punctureR v)) 1 (w v).val height J) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ label, (bufferedProductFamily M H hH η₀
        (CenteredMomentNaturalRowSource.excluded (NL v).character (punctureL v)) label).modulus.absNorm ≤ Z^d) →
      (∀ v ∈ S, ∀ label, (bufferedProductFamily M H hH η₀
        (CenteredMomentNaturalRowSource.excluded (NR v).character (punctureR v)) label).modulus.absNorm ≤ Z^d) →
      (∀ v ∈ S, t v = tbase v+2*Real.pi*(firstU v-firstTheta v)) →
      (∀ v ∈ S, |tbase v| ≤ Z^ν ∧ |firstU v| ≤ Z^ν ∧ |firstTheta v| ≤ Z^ν) →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ v ∈ S, ∀ j, |freq v j| ≤ Z^ν) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      ∀ supportLoss clipLoss commonLoss : ℝ, supportLoss+clipLoss+commonLoss ≤ lengthLoss →
      (∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^A) →
      (∀ v ∈ S, Z^(c+c₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ∧
        Z^(c+d₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ)) →
      (∀ v ∈ S, (max 1 (s v).input.upper)^Fintype.card Slot ≤ Z^supportLoss) →
      Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ clipLoss →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA →

      targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000 →
      (∑ v ∈ S, ∑ D ∈ Ds v,
        ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ) *
          ((UniqueFactorizationMonoid.moebius D : ℂ)*
            ((Z^(A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss) : ℝ) : ℂ)*rayWeight v) *
          ((s v).withProjector D).toKernelLabel.kernelRow (t v) (z v) Wkernel (K v) (Radius v) (n v)‖) ≤
        C*(retainedProfileEnvelope S s aSource+128/aSource*(originalAbsoluteEnvelope S s plainBound₁ plainBound₂)^2+1)*Z^(π+A-c+R₁+E+Bc-144011/109800000) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_kernel_contribution η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      Wkernel decay tailA 1 targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
  have hτ : 0 < τ := hν.trans hντ
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh,twoStageFrequency_uniform τ ν hντ,
    uniform_height_budget dmin τ ηaux I hτ.le hη.le hheight] with Z hZ hfrequency hheightBudget
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t K Radius tbase firstU firstTheta n rayWeight
    σ freq θ slotWidth aSource haSource hray hsourceIntervals hsourceNorm hprojectorNorm hphysical
    parentL parentR NL NR punctureL punctureR hpunctureL hpunctureR hplain hmatch
    hrowL hrowR hscale hprimeScale hcondL hcondR hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have hgate (x : ℝ) (hx : |x| ≤ Z^τ) : |x|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ := by
    have hiR : (2 : ℝ) ≤ (3*i+2 : ℕ) := by exact_mod_cast (show 2 ≤ 3*i+2 by omega)
    have hTpos : 0 ≤ Z^τ := Real.rpow_nonneg hZpos.le _
    nlinarith [mul_le_mul_of_nonneg_right hiR hTpos]
  have hshift (v) (hv : v ∈ S) (shift ξ u : ℝ)
      (hs : |shift| ≤ Z^ν) (hξ : ‖ξ‖ ≤ Z^ν) (hu : ‖u‖ ≤ Z^ν) :
      |t v+2*Real.pi*(u-ξ)+shift| ≤ Z^τ := by
    have hh := hfrequency (tbase v) shift (firstU v) (firstTheta v) u ξ
      (hinputfreq v hv).1 hs (hinputfreq v hv).2.1 (hinputfreq v hv).2.2
      (by simpa only [Real.norm_eq_abs] using hu) (by simpa only [Real.norm_eq_abs] using hξ)
    rw [hteq v hv]
    convert hh using 1
    congr 1
    unfold twoStageFrequency
    ring
  have hfour := hheightBudget d hd i hi
  have htwo : (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux := by
    have hb : 1 ≤ 3+(3*i+2 : ℕ)*Z^τ := by
      have hp : 0 ≤ (3*i+2 : ℕ)*Z^τ := by positivity
      linarith
    exact (pow_le_pow_right₀ hb (by omega : 2 ≤ 4)).trans hfour
  apply hZ.2 d P W (hdmin.le.trans hd) hdmax' hbase hT hPB hWB p hp i hi hheightBin
    unit S w hw R hR hsup heq hproj hbin hnorm hNw hNr s Ds z t K Radius n rayWeight
    σ freq θ slotWidth aSource haSource hray hsourceIntervals hsourceNorm hprojectorNorm hphysical
    parentL parentR NL NR punctureL punctureR hpunctureL hpunctureR hplain hmatch hrowL hrowR
    hscale hprimeScale hcondL hcondR ?_ hfour htwo hσrange ?_
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂ ?_
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂ hgeometryLoss hlengthLoss
    hW hP htotal htailA (fun v hv => (hvolume v hv).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith : A ≤ 1))) htarget
  · intro ξ u₁ u₂ hξ hu₁ hu₂ v hv
    constructor
    · apply hgate
      simpa only [add_zero] using hshift v hv 0 ξ u₁ (by simp; positivity) hξ hu₁
    · apply hgate
      simpa only [add_zero] using hshift v hv 0 (-ξ) u₂ (by simp; positivity)
        (by simpa only [norm_neg] using hξ) hu₂
  · intro ξ u₁ u₂ hξ hu₁ hu₂ v hv j
    exact ⟨hgate _ (hshift v hv (freq v j) ξ u₁ (hslotfreq v hv j) hξ hu₁),
      hgate _ (hshift v hv (freq v j) (-ξ) u₂ (hslotfreq v hv j)
        (by simpa only [norm_neg] using hξ) hu₂)⟩
  · intro ξ u₁ u₂ hξ hu₁ hu₂ v hv q hq
    have hh := (s v).active_full_lengths_with_common_loss (Ds v) (t v+2*Real.pi*(u₁-ξ))
      (t v+2*Real.pi*(u₂-(-ξ))) (dyadicScale (n v 2)) (dyadicScale (n v 3)) (z v)
      q hq Z A c c₂ d₂ supportLoss clipLoss commonLoss b₁ b₂plain hZ.1
      (fun j => (hprimeScale v hv j).1) (hvolume v hv)
      (hcommonDyads v hv).1 (hcommonDyads v hv).2 (hsupport v hv) hclip
    exact ⟨hh.1.trans (by linarith),hh.2.trans (by linarith)⟩

end FixedData
#print axioms actual_joint_high_kernel_from_geometry
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighKernelGeometry -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowCommonBinSource ; sha256 114bae290918a90d71bf22f4102eefc64133462ed23a6875a25e669cdf5dfee9 -/
section














/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot ConcretePrimeRowBridge LocalMoment LocalMomentSourceAudit
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
open CenteredMomentEnergyCapacityRemoval
open CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedChildren
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedZero
open CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentAllocatedNaturalSource
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance lowCommonBinSourceFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

open CanonicalQuadraticSieve CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialSource CenteredMomentSourceProfileMass CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialCost CenteredMomentCommonLinearNormalization

open ActualEisensteinCubic RayFourExpansion CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentEnergyChildState
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit CenteredMomentExceptionalAmplitudePair

theorem actual_second_low_source_of_common_bin
    (W : ℝ → ℂ) (aslot bslot a b Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hL : 0 ≤ L) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss)
    (Mslot εmask : ℝ) (hMslot : 0 ≤ Mslot) (hεmask : 0 < εmask)
    (loInput hiInput : α → ℝ) (Bcommon δcommon : ℝ) (hBcommon : 0 ≤ Bcommon) (hδcommon : 0 < δcommon)
    (ηfirst : Character) (parentLoss : ℝ) (hparentLoss : 0 < parentLoss)
    (ξconductor : ℝ) (hξconductor : 0 < ξconductor) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)},
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (v height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (p : Profiles a b) (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      src.X₁ ≤ Z^L → src.X₂ ≤ Z^L → src.Y₁ ≤ Z^L → src.Y₂ ≤ Z^L →
      ∀ (C₁ D₁ C₂ D₂ Rmask seed Lproj : Ideal O) (hC₁ : Supported C₁)
        (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂),
      primeSupport C₂ = primeSupport D₂ →
      ∀ (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
      activeConductor C₁ D₁ = (u : O)*∏ i,activePrimary C₁ D₁ i ∧
      ∀ left : Bool, let parent := firstSideCharacter F left
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family parent C₂ D₂ hC₂ hD₂ U family →
      ∀ (T : Ideal O) (hTpick : T = C₂ ∨ T = D₂),
      Rmask ≠ 0 → seed ∣ C₁*T → Squarefree Lproj →
      ((C₁*T).absNorm : ℝ) ≤ Z^Bcommon → (Lproj.absNorm : ℝ) ≤ Z^Bcommon →
      ∀ (t : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ) (rows : Finset O)
        (Wrad : 𝓢(ℝ,ℂ)) (Kcut : ℝ) (n : Fin 4 → ℤ)
        (Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip : ℝ),
      0 < Kcut → 0 < Hsource → Real.logb Z Hsource ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 37/10000 → 0 ≤ omegaLoss → 3/500 ≤ allowance →
      0 ≤ profileLoss → 0 ≤ clip → Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let c := Real.logb Z (C₁.absNorm : ℝ)
      let d₁ := Real.logb Z (D₁.absNorm : ℝ)
      let r₁ := Real.logb Z (normValue (activeConductor C₁ D₁))
      let e₁ := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E₁))
      let radius := frequencyRadius (jointSecondNominal C₁ Hsource Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss) Z ξ
      let nominal := jointLowNominal Mparent c d₁ (3/500) omegaLoss
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ))
      let pad := 2*sourceLoss+parentLoss+ξ/2+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → nominal+pad ≤ Mcap → nominal+pad+Bmask+ξconductor ≤ d →
      pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 401/9000000 →
      ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows Wrad Kcut n ≠ 0,
      ∀ χ : RayCharacter,
      let s := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χ (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      ∀ (reflect : Bool) (low : O → Prop) (abin : ℝ) (k : ℕ),
      ∀ (holes : O → JointRelativeLabel ηfirst (Option (α × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ z label,holes z label ≠ 0),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState s).radial.keep z, low z →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes z) (hholes z) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left (lowSignedRow reflect z)
            (lowSignedRow_ne_zero reflect z (s.row_ne_zero z hz.1)))) →
      (∀ i, |v+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      sourceEnergy (withHeight src s.character v) (restrictedLowRadial s.radial low)
        (C₁*T) ((supported_mul_iff _ _).mpr ⟨hC₁,second_selected_supported hC₂ hD₂ hTpick⟩) Rmask seed Lproj ≤
        Cbound*((Rmask*(C₁*T)).radical.absNorm : ℝ)^εmask*profileCost src*diagonalControl s.radial.profile*
          (p.control S)^2*(1+|v|+height)^degree *
          Z^(δcommon+(nominal+allowance-401/9000000))/(((C₁*T).absNorm : ℝ)*Lproj.absNorm) := by
  obtain ⟨degree,S,hmain⟩ := actual_second_low_source M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain,eventually_actual_second_signed_low_gate (Slot := α) M H hH η₀ 2 ξconductor hξconductor,
    eventually_actual_low_state_width ηfirst parentLoss hparentLoss] with Z hmain hgate hwidth
  intro hZ θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ C₁ D₁ C₂ D₂ Rmask seed Lproj hC₁ hD₁ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F
  let u := firstSideDictionaryUnit ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  obtain ⟨hu,hgate⟩ := hgate.2 ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  refine ⟨hu,?_⟩
  intro left parent U family hfamily T hTpick hR hseed hLproj hCcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    c d₁ r₁ e₁ radius nominal pad hpad hMcapSource hconductorSource hbudgetSource hne χ s reflect low abin k holes hholes
    habin habinTop hbase hT hbin hfreqGate hheightSource
  have hparent : parent = F.left ∨ parent = F.right := by cases left <;> simp [parent,firstSideCharacter]
  have hswidth : s.width ≤ nominal+pad := hwidth hZ C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F parent hparent
    C₂ D₂ hC₂ hD₂ U family hfamily t columns β rows Wrad Kcut n Hsource A Mparent omegaLoss ξ sourceLoss Bmask
    hKcut hHsource hmask hsource hne χ (internalQ Q η₀)
  have hlow : ∀ z, ∀ hz : (supportedNaturalState s).radial.keep z, low z →
      NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM rfl d τ e abin k z hz := by
    intro z hz hl
    exact hgate left C₂ D₂ hC₂ hD₂ hCD₂ U family hfamily (Rmask*(C₁*T))
      (mul_ne_zero hR (mul_ne_zero hC₁.1 (second_selected_supported hC₂ hD₂ hTpick).1))
      (by rcases hTpick with rfl | rfl
          · exact Or.inl ((dvd_mul_left _ C₁).trans (dvd_mul_left _ Rmask))
          · exact Or.inr ((dvd_mul_left _ C₁).trans (dvd_mul_left _ Rmask))) χ Bmask d s rfl rfl
      (by linarith) Q hQM rfl hQ72 reflect z hz τ e abin k he (holes z) (hholes z) (hbin z hz hl)
  exact hmain hZ θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ C₁ D₁ C₂ D₂ Rmask seed Lproj hC₁ hD₁ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F parent hparent U family hfamily T hTpick hR hseed hLproj hCcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    hpad hMcapSource hbudgetSource hne χ low abin k habin habinTop hbase hT hlow hfreqGate hheightSource

#print axioms actual_second_low_source_of_common_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowCommonBinSource -/
