/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.reserve_local_20261013.Bundles.B016
import Submissions.reserve_local_20261013.Bundles.B019
import Submissions.reserve_local_20261013.Bundles.B034
import Submissions.reserve_local_20261013.Bundles.B059
import Submissions.reserve_local_20261013.Bundles.B064
import Submissions.reserve_local_20261013.Bundles.B065
import Submissions.reserve_local_20261013.Bundles.B066
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockCount

/- BEGIN ORIGINAL MODULE Analytic.JointFirstLocalSector ; sha256 ec624694093a122e283a32e1a379ba91c534fdcac6a51311982fa5b851351ed5 -/
section



/-! The literal first-sector conclusion from bounded Fourier joint
energies, preserving the NC/volume and ND/volume normalizations. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem joint_first_centered_sector_from_local_joint_targets
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (Mwin : Fin 4 → ℝ) (hMwin : ∀ i, 0 ≤ Mwin i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ Mwin i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay : ℕ) (ν B lower : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
      (q : FirstJointLabel ι) (Z M A δ a window Ch Ct : ℝ), 1 < Z → 0 < a →
      0 ≤ Ch → 0 ≤ Ct → lower ≤ q.leftTargetWidth Z A → lower ≤ q.rightTargetWidth Z A →
      ∀ (t K₀ H₀ A₀ B₀ : Λ → ℝ),
      (∀ z ∈ rows, z ≠ 0) →
      (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) → (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      (∀ l ∈ labels, a*Z^A ≤ ((s l).C.absNorm : ℝ)*Real.exp window*A₀ l) →
      (∀ l ∈ labels, a*Z^A ≤ ((s l).D.absNorm : ℝ)*Real.exp window*B₀ l) →
      (∀ l ∈ labels, ((s l).C.absNorm : ℝ) ≤ Z^δ*(q.C.absNorm : ℝ)) →
      (∀ l ∈ labels, ((s l).D.absNorm : ℝ) ≤ Z^δ*(q.D.absNorm : ℝ)) →
      (∀ l ∈ labels, q.activeWidth Z/2+q.punctureWidth Z ≤
        (s l).activeWidth Z/2+(s l).punctureWidth Z) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (Z^M) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ (U : ((l : Λ) × (s l).SourceIndex) → 𝓢(ℝ, ℂ))
        (H : ((l : Λ) × (s l).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels s, 0 < H k) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z : O,
        0 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z ∈ rows,
        1 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
        (∑ k ∈ firstSourceLabels labels s,
          ((s k.1).sourceChild k.2).leftEnergy
            (t k.1+2*Real.pi*(w-θ)) (U k) (H k)) ≤
          (Z^A/(q.C.absNorm : ℝ))*(Ch*Z^(q.leftTargetWidth Z A))) →
      (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
        (∑ k ∈ firstSourceLabels labels s,
          ((s k.1).sourceChild k.2).rightEnergy
            (t k.1+2*Real.pi*(w-(-θ))) (U k) (H k)) ≤
          (Z^A/(q.D.absNorm : ℝ))*(Ch*Z^(q.rightTargetWidth Z A))) →
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).leftCoarse (U k) (H k)) ≤
          (Z^A/(q.C.absNorm : ℝ))*(Ct*Z^B) →
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).rightCoarse (U k) (H k)) ≤
          (Z^A/(q.D.absNorm : ℝ))*(Ct*Z^B) →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) *
        (s l).sourceBlock (t l) rows W V (Z^M) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ / Z^A ≤
          C * (Ch+Ct) * (Real.exp window/a) * Z^(M+δ) := by
  obtain ⟨N,hpoly⟩ := two_variable_polynomial_extension_even ν B lower hν
  obtain ⟨C, hC, hc⟩ := joint_first_centered_blocks_from_scalar_cap (ι := ι) W V Mwin hMwin hV
    hV₂c hV₂s hV₃c hV₃s decay N N N N
  refine ⟨N,C,hC,?_⟩
  intro Λ inst labels rows s q Z M A δ a window Ch Ct hZ ha hCh hCt htl htr t K₀ H₀ A₀ B₀ hrows
    hK₀ hH₀ hA₀ hB₀ hl hr hNC hND hscalarWidth hV₀ hV₁ U H hH hU hmajor hleft hright hcoarseL hcoarseR
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hNqC : 0 < (q.C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr q.hC.1)
  have hNqD : 0 < (q.D.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr q.hD.1)
  have hroot : 0 < Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm) :=
    Real.sqrt_pos.mpr (mul_pos hNqC hNqD)
  let F := (Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ)*
    Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm)
  have hF : 0 < F := by dsimp [F]; positivity
  have hleft' := hpoly (q.leftTargetWidth Z A) htl Z
    ((Z^A/(q.C.absNorm : ℝ))*Ch) ((Z^A/(q.C.absNorm : ℝ))*Ct) hZ.le
    (by positivity) (by positivity)
    (fun θ w => ∑ k ∈ firstSourceLabels labels s,
      ((s k.1).sourceChild k.2).leftEnergy (t k.1+2*Real.pi*(w-θ)) (U k) (H k))
    (by simpa only [mul_assoc] using hleft)
    (by
      intro θ w
      apply (Finset.sum_le_sum (fun k hk =>
        ((s k.1).sourceChild k.2).leftEnergy_le_coarse _ (U k) (H k) (hH k hk))).trans
      simpa only [mul_assoc] using hcoarseL)
  have hright' := hpoly (q.rightTargetWidth Z A) htr Z
    ((Z^A/(q.D.absNorm : ℝ))*Ch) ((Z^A/(q.D.absNorm : ℝ))*Ct) hZ.le
    (by positivity) (by positivity)
    (fun θ w => ∑ k ∈ firstSourceLabels labels s,
      ((s k.1).sourceChild k.2).rightEnergy (t k.1+2*Real.pi*(w-(-θ))) (U k) (H k))
    (by simpa only [mul_assoc] using hright)
    (by
      intro θ w
      apply (Finset.sum_le_sum (fun k hk =>
        ((s k.1).sourceChild k.2).rightEnergy_le_coarse _ (U k) (H k) (hH k hk))).trans
      simpa only [mul_assoc] using hcoarseR)
  have hh := hc labels rows s t (fun _ => Z^M) K₀ H₀ A₀ B₀
    hrows (fun _ => Real.rpow_pos_of_pos hz _) hK₀ hH₀ hA₀ hB₀
    F (Z^A) (q.C.absNorm : ℝ) (q.D.absNorm : ℝ) hF (Real.rpow_pos_of_pos hz _)
    hNqC hNqD
    (fun l hmem => (s l).sector_scalar_cap q Z M A δ (A₀ l) (B₀ l) a window hZ
      (hA₀ l) (hB₀ l) ha (hl l hmem) (hr l hmem) (hNC l hmem) (hND l hmem)
      (hscalarWidth l hmem))
    hV₀ hV₁ U H hH hU hmajor ((Ch+Ct)*Z^(q.leftTargetWidth Z A)) ((Ch+Ct)*Z^(q.rightTargetWidth Z A))
    (by positivity) (by positivity)
    (by simpa only [←mul_add,mul_assoc] using hleft')
    (by simpa only [←mul_add,mul_assoc] using hright')
  have hFdiv : F/Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm) =
      (Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ) := by
    dsimp only [F]
    exact mul_div_cancel_right₀ _ hroot.ne'
  rw [hFdiv,Real.sqrt_mul (add_nonneg hCh hCt),Real.sqrt_mul (add_nonneg hCh hCt)] at hh
  have hpair : (Real.sqrt (Ch+Ct)*Real.sqrt (Z^(q.leftTargetWidth Z A)))*
      (Real.sqrt (Ch+Ct)*Real.sqrt (Z^(q.rightTargetWidth Z A))) =
      (Ch+Ct)*(Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A))) := by
    calc
      _ = (Real.sqrt (Ch+Ct))^2*
          (Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A))) := by ring
      _ = _ := by rw [Real.sq_sqrt (add_nonneg hCh hCt)]
  rw [hpair] at hh
  have hbudget := actual_first_joint_rpow_budget q Z M A hZ
  change Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z)*
    Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A)) ≤ Z^M at hbudget
  calc
    _ ≤ C*((Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ))*
        ((Ch+Ct)*(Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A)))) := hh
    _ = (C*(Ch+Ct)*(Real.exp window/a)*Z^δ)*
        (Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z)*
          Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A))) := by
      rw [Real.rpow_add hz]
      ring
    _ ≤ (C*(Ch+Ct)*(Real.exp window/a)*Z^δ)*Z^M :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by rw [Real.rpow_add hz]; ring

#print axioms joint_first_centered_sector_from_local_joint_targets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstLocalSector -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstParentWidth ; sha256 51fa60b6db58e06199f68eeb8654009c1e92ae15e58d39e7b0dab2b6540009a7 -/
section



/-! The first child character's conductor width is its active and selected
common widths plus a fixed-family constant, uniformly in all labels. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentSecondHeightFamily ConcreteTraceCRT
open CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization
open RayFourExpansion
local notation "O" => HeckeFamily.O

theorem eventually_first_parent_width (η : Character) (ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
        (ξ₁ ξ₂ : RayCharacter) (F : FixedPair η C D hC E ξ₁ ξ₂),
      let width := Real.logb Z (normValue (activeConductor C D))+
        Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E))+ξ
      Real.logb Z (F.left.modulus.absNorm : ℝ) ≤ width ∧
        Real.logb Z (F.right.modulus.absNorm : ℝ) ≤ width := by
  let K : ℝ := fixedPresentationCost*(η.modulus.absNorm : ℝ)
  have hK : 0 < K := mul_pos fixedPresentationCost_pos
    (CenteredMomentFirstScale.norm_pos η.modulus η.modulus_ne_bot)
  filter_upwards [(tendsto_rpow_atTop hξ).eventually (eventually_ge_atTop K),
    eventually_gt_atTop (1 : ℝ)] with Z hKcap hZ
  refine ⟨hZ,?_⟩
  intro C D hC E ξ₁ ξ₂ F
  have hN (τ : Character)
      (hmod : τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*activeConductor C D}) :
      Real.logb Z (τ.modulus.absNorm : ℝ) ≤
        Real.logb Z (normValue (activeConductor C D))+
          Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E))+ξ := by
    have he : 0 < normValue (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) :=
      normValue_pos _ (primeSubsetGenerator_ne_zero _ _)
    have hr : 0 < normValue (activeConductor C D) :=
      normValue_pos _ (finitePrimeModulus_ne_zero (activePrime C D))
    have hid := fixed_presentation_norm η τ C D E hmod
    rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span] at hid
    change (τ.modulus.absNorm : ℝ) = K*
      normValue (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)*
        normValue (activeConductor C D) at hid
    have hklog := Real.logb_le_logb_of_le hZ hK hKcap
    rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hklog
    rw [hid,Real.logb_mul (mul_pos hK he).ne' hr.ne',Real.logb_mul hK.ne' he.ne']
    linarith
  exact ⟨hN F.left F.left_modulus,hN F.right F.right_modulus⟩

#print axioms eventually_first_parent_width
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstParentWidth -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstVariableLocalSector ; sha256 ecfb54dcfdf1400ac3cdee7208e94b20e3f5f0b4e76501a956f25e0e99dc34de -/
section



/-! The literal first-sector conclusion from bounded Fourier joint
energies, preserving the NC/volume and ND/volume normalizations. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem joint_first_variable_centered_sector_from_local_joint_targets
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (Mwin : Fin 4 → ℝ) (hMwin : ∀ i, 0 ≤ Mwin i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ Mwin i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay : ℕ) (ν B lower : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Λ → Finset O) (s : Λ → FirstJointLabel ι)
      (q : FirstJointLabel ι) (Z M A δ a window Ch Ct : ℝ), 1 < Z → 0 < a →
      0 ≤ Ch → 0 ≤ Ct → lower ≤ q.leftTargetWidth Z A → lower ≤ q.rightTargetWidth Z A →
      ∀ (t K₀ H₀ A₀ B₀ : Λ → ℝ),
      (∀ l, ∀ z ∈ rows l, z ≠ 0) →
      (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) → (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      (∀ l ∈ labels, a*Z^A ≤ ((s l).C.absNorm : ℝ)*Real.exp window*A₀ l) →
      (∀ l ∈ labels, a*Z^A ≤ ((s l).D.absNorm : ℝ)*Real.exp window*B₀ l) →
      (∀ l ∈ labels, ((s l).C.absNorm : ℝ) ≤ Z^δ*(q.C.absNorm : ℝ)) →
      (∀ l ∈ labels, ((s l).D.absNorm : ℝ) ≤ Z^δ*(q.D.absNorm : ℝ)) →
      (∀ l ∈ labels, q.activeWidth Z/2+q.punctureWidth Z ≤
        (s l).activeWidth Z/2+(s l).punctureWidth Z) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (Z^M) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows l, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ (U : ((l : Λ) × (s l).SourceIndex) → 𝓢(ℝ, ℂ))
        (H : ((l : Λ) × (s l).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels s, 0 < H k) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z : O,
        0 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z ∈ rows k.1,
        1 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
        (∑ k ∈ firstSourceLabels labels s,
          ((s k.1).sourceChild k.2).leftEnergy
            (t k.1+2*Real.pi*(w-θ)) (U k) (H k)) ≤
          (Z^A/(q.C.absNorm : ℝ))*(Ch*Z^(q.leftTargetWidth Z A))) →
      (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
        (∑ k ∈ firstSourceLabels labels s,
          ((s k.1).sourceChild k.2).rightEnergy
            (t k.1+2*Real.pi*(w-(-θ))) (U k) (H k)) ≤
          (Z^A/(q.D.absNorm : ℝ))*(Ch*Z^(q.rightTargetWidth Z A))) →
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).leftCoarse (U k) (H k)) ≤
          (Z^A/(q.C.absNorm : ℝ))*(Ct*Z^B) →
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).rightCoarse (U k) (H k)) ≤
          (Z^A/(q.D.absNorm : ℝ))*(Ct*Z^B) →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) *
        (s l).sourceBlock (t l) (rows l) W V (Z^M) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ / Z^A ≤
          C * (Ch+Ct) * (Real.exp window/a) * Z^(M+δ) := by
  obtain ⟨N,hpoly⟩ := two_variable_polynomial_extension_even ν B lower hν
  obtain ⟨C, hC, hc⟩ := joint_first_variable_centered_blocks_from_scalar_cap (ι := ι) W V Mwin hMwin hV
    hV₂c hV₂s hV₃c hV₃s decay N N N N
  refine ⟨N,C,hC,?_⟩
  intro Λ inst labels rows s q Z M A δ a window Ch Ct hZ ha hCh hCt htl htr t K₀ H₀ A₀ B₀ hrows
    hK₀ hH₀ hA₀ hB₀ hl hr hNC hND hscalarWidth hV₀ hV₁ U H hH hU hmajor hleft hright hcoarseL hcoarseR
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hNqC : 0 < (q.C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr q.hC.1)
  have hNqD : 0 < (q.D.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr q.hD.1)
  have hroot : 0 < Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm) :=
    Real.sqrt_pos.mpr (mul_pos hNqC hNqD)
  let F := (Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ)*
    Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm)
  have hF : 0 < F := by dsimp [F]; positivity
  have hleft' := hpoly (q.leftTargetWidth Z A) htl Z
    ((Z^A/(q.C.absNorm : ℝ))*Ch) ((Z^A/(q.C.absNorm : ℝ))*Ct) hZ.le
    (by positivity) (by positivity)
    (fun θ w => ∑ k ∈ firstSourceLabels labels s,
      ((s k.1).sourceChild k.2).leftEnergy (t k.1+2*Real.pi*(w-θ)) (U k) (H k))
    (by simpa only [mul_assoc] using hleft)
    (by
      intro θ w
      apply (Finset.sum_le_sum (fun k hk =>
        ((s k.1).sourceChild k.2).leftEnergy_le_coarse _ (U k) (H k) (hH k hk))).trans
      simpa only [mul_assoc] using hcoarseL)
  have hright' := hpoly (q.rightTargetWidth Z A) htr Z
    ((Z^A/(q.D.absNorm : ℝ))*Ch) ((Z^A/(q.D.absNorm : ℝ))*Ct) hZ.le
    (by positivity) (by positivity)
    (fun θ w => ∑ k ∈ firstSourceLabels labels s,
      ((s k.1).sourceChild k.2).rightEnergy (t k.1+2*Real.pi*(w-(-θ))) (U k) (H k))
    (by simpa only [mul_assoc] using hright)
    (by
      intro θ w
      apply (Finset.sum_le_sum (fun k hk =>
        ((s k.1).sourceChild k.2).rightEnergy_le_coarse _ (U k) (H k) (hH k hk))).trans
      simpa only [mul_assoc] using hcoarseR)
  have hh := hc labels rows s t (fun _ => Z^M) K₀ H₀ A₀ B₀
    hrows (fun _ => Real.rpow_pos_of_pos hz _) hK₀ hH₀ hA₀ hB₀
    F (Z^A) (q.C.absNorm : ℝ) (q.D.absNorm : ℝ) hF (Real.rpow_pos_of_pos hz _)
    hNqC hNqD
    (fun l hmem => (s l).sector_scalar_cap q Z M A δ (A₀ l) (B₀ l) a window hZ
      (hA₀ l) (hB₀ l) ha (hl l hmem) (hr l hmem) (hNC l hmem) (hND l hmem)
      (hscalarWidth l hmem))
    hV₀ hV₁ U H hH hU hmajor ((Ch+Ct)*Z^(q.leftTargetWidth Z A)) ((Ch+Ct)*Z^(q.rightTargetWidth Z A))
    (by positivity) (by positivity)
    (by simpa only [←mul_add,mul_assoc] using hleft')
    (by simpa only [←mul_add,mul_assoc] using hright')
  have hFdiv : F/Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm) =
      (Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ) := by
    dsimp only [F]
    exact mul_div_cancel_right₀ _ hroot.ne'
  rw [hFdiv,Real.sqrt_mul (add_nonneg hCh hCt),Real.sqrt_mul (add_nonneg hCh hCt)] at hh
  have hpair : (Real.sqrt (Ch+Ct)*Real.sqrt (Z^(q.leftTargetWidth Z A)))*
      (Real.sqrt (Ch+Ct)*Real.sqrt (Z^(q.rightTargetWidth Z A))) =
      (Ch+Ct)*(Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A))) := by
    calc
      _ = (Real.sqrt (Ch+Ct))^2*
          (Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A))) := by ring
      _ = _ := by rw [Real.sq_sqrt (add_nonneg hCh hCt)]
  rw [hpair] at hh
  have hbudget := actual_first_joint_rpow_budget q Z M A hZ
  change Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z)*
    Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A)) ≤ Z^M at hbudget
  calc
    _ ≤ C*((Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ))*
        ((Ch+Ct)*(Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A)))) := hh
    _ = (C*(Ch+Ct)*(Real.exp window/a)*Z^δ)*
        (Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z)*
          Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A))) := by
      rw [Real.rpow_add hz]
      ring
    _ ≤ (C*(Ch+Ct)*(Real.exp window/a)*Z^δ)*Z^M :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by rw [Real.rpow_add hz]; ring

#print axioms joint_first_variable_centered_sector_from_local_joint_targets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstVariableLocalSector -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSourceCaps ; sha256 fb440ea82001a81c078d335caf8f74693a183487f1b741d6678d0f01fcb7c602 -/
section




/-! Uniform size gates derived from the actual source blocks and common
ideal arithmetic. These estimates precede the live second labels. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonHarmonicMass
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockCount
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition CenteredMomentDyadicCount
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondActiveCount
open CenteredMomentFirstSourceConductorCaps CenteredMomentSourceRow CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

theorem actual_common_cumulative_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed C₀ L : Ideal O) (hC₀ : Supported C₀)
    (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (p : ActiveLabel (commonSecondColumns (original s R seed) C₀ hC₀)
      (commonSecondBeta (original s R seed) C₀ L)) :
    ((C₀*p.val.1).absNorm : ℝ) ≤ sourceRadius s ∧
      ((C₀*p.val.2).absNorm : ℝ) ≤ sourceRadius s := by
  have hnorm := commonSecond_source_norm_cap (original s R seed) C₀ L hC₀ (sourceRadius s)
    (fun I _ hI => (CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hI).2)
  have hn := commonLabel_norm_bounds _ _ _ hnorm _ _ p.property
  have hNC : (0 : ℝ) < C₀.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC₀.1)
  constructor
  · simpa only [map_mul,Nat.cast_mul,mul_comm] using (le_div_iff₀ hNC).mp hn.1
  · simpa only [map_mul,Nat.cast_mul,mul_comm] using (le_div_iff₀ hNC).mp hn.2

theorem source_block_row_dyad_bound
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D))
    (K R H : ℝ) (hR : 0 ≤ R) (n : SourceBlocks C D U K R H) :
    dyadicScale (n 1 : ℤ) ≤ 4*max 1 (4*R) := by
  let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  have hA : A ≠ 0 := mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hn := ((mem_indices_iff_scale 1 (max 1 (4*R/normValue A)) (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)) (n 1)).mp
      (n 1).property).2
  apply hn.trans
  apply mul_le_mul_of_nonneg_left (max_le_max le_rfl _) (by norm_num)
  exact div_le_self (by positivity) (normValue_ge_one A hA)

theorem eventually_source_block_row_power (L Cr tailRows : ℝ) (hL : 0 ≤ L)
    (hCr : 0 < Cr) (htail : L+1 ≤ tailRows) :
    ∀ᶠ Z : ℝ in Filter.atTop, ∀ (C D : Ideal O) (hC : Supported C)
      (U : Finset (CommonIndex C D)) (K R H : ℝ),
      1 ≤ Z → 0 ≤ R → R ≤ Cr*Z^L → ∀ n : SourceBlocks C D U K R H,
      dyadicScale (n 1 : ℤ) ≤ Z^tailRows := by
  filter_upwards [Filter.eventually_ge_atTop (4*max 1 (4*Cr))] with Z hZcap
  intro C D hC U K R H hZ hR hRcap n
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hpow : 1 ≤ Z^L := Real.one_le_rpow hZ hL
  have hm : max 1 (4*R) ≤ max 1 (4*Cr)*Z^L := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) hpow
    · calc
        4*R ≤ (4*Cr)*Z^L := by linarith
        _ ≤ max 1 (4*Cr)*Z^L := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  calc
    _ ≤ 4*max 1 (4*R) := source_block_row_dyad_bound C D hC U K R H hR n
    _ ≤ (4*max 1 (4*Cr))*Z^L := by nlinarith
    _ ≤ Z*Z^L := mul_le_mul_of_nonneg_right hZcap (by positivity)
    _ = Z^(L+1) := by rw [Real.rpow_add hz,Real.rpow_one]; ring
    _ ≤ Z^tailRows := Real.rpow_le_rpow_of_exponent_le hZ htail

theorem common_subset_norm_le_frequency (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    ((∏ P ∈ U,P.val).absNorm : ℝ) ≤ normValue (commonFrequencyGenerator C D) := by
  have hP (P : CommonIndex C D) : (1 : ℝ) ≤ P.val.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (commonPrime_supported_ideal C D hC P).1)
  have hp := Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ U)
    (fun P _ => (hP P).trans' (by norm_num)) (fun P _ _ => hP P)
  change (∏ P ∈ U,(P.val.absNorm : ℝ)) ≤ ∏ P : CommonIndex C D,(P.val.absNorm : ℝ) at hp
  simp only [map_prod,Nat.cast_prod]
  apply hp.trans
  simp only [normValue,commonFrequencyGenerator,span_finset_product,←Ideal.span_singleton_pow,
    map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]
  simp_rw [commonPrime_span C D hC]
  apply Finset.prod_le_prod₀ (fun P _ => (hP P).trans' (by norm_num))
  intro P hPmem
  simpa only [pow_one] using pow_le_pow_right₀ (hP P)
    (show 1 ≤ min (leftExponent C D P) (rightExponent C D P) from
      le_min (leftExponent_pos C D P) (rightExponent_pos C D P))

theorem joint_low_nominal_le_parent (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z M c d a omega : ℝ)
    (hZ : 1 < Z) (ha : 0 ≤ a) (hω : 0 ≤ omega) :
    jointLowNominal M c d a omega (Real.logb Z (normValue (commonFrequencyGenerator C D)))
      (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) ≤ M := by
  have htpos : (0 : ℝ) < (∏ P ∈ U,P.val).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun P _ => (commonPrime_supported_ideal C D hC P).1)))
  have hlog := Real.logb_le_logb_of_le hZ htpos (common_subset_norm_le_frequency C D hC U)
  dsimp only [jointLowNominal]
  linarith [le_max_right (c-d) 0]

theorem joint_low_nominal_lower_of_common_cap
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (Z B M c d a omega : ℝ) (hZ : 1 < Z) (hcap : (C.absNorm : ℝ) ≤ Z^B) :
    M-max (c-d) 0-6*a-omega-B ≤
      jointLowNominal M c d a omega (Real.logb Z (normValue (commonFrequencyGenerator C D)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) := by
  have hd := (commonFrequencyGenerator_dvd C D hC hD hCD).1
  have hdiv : Ideal.span {commonFrequencyGenerator C D} ∣ C := by
    simpa only [primary_span_supported C hC] using
      (Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr hd)
  have hgcap : normValue (commonFrequencyGenerator C D) ≤ Z^B :=
    (divisor_norm_le _ _ hC.1 hdiv).trans hcap
  have hglog := Real.logb_le_logb_of_le hZ
    (normValue_pos _ (commonFrequencyGenerator_ne_zero C D hC)) hgcap
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hglog
  have htpos : (1 : ℝ) ≤ (∏ P ∈ U,P.val).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun P _ => (commonPrime_supported_ideal C D hC P).1)))
  have htlog := Real.logb_nonneg hZ htpos
  dsimp only [jointLowNominal]
  linarith

#print axioms joint_low_nominal_lower_of_common_cap
#print axioms actual_common_cumulative_norm
#print axioms eventually_source_block_row_power
#print axioms joint_low_nominal_le_parent
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSourceCaps -/

/- BEGIN ORIGINAL MODULE Analytic.JointMatchesSlotGates ; sha256 9b1bcde2e04c437d3eccdbec5747ccf10ea3a25aa76998257f8e032ed7bd8e15 -/
section




/-! The actual source dictionary gives the coefficient gates needed by
the shifted high product. Ray characters disappear only on the literal
prime pool; all real and imaginary Mellin shifts remain in the data. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckePrimeAnnular
open CenteredMomentCommonRadialData CenteredMomentAllocatedRayDictionary
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H)
variable (s : Input Slot) (η₀ : Character)
  (θ : Slot → RayQuotient.Characters M H) (w σ freq : Slot → ℝ)
  (W : ℝ → ℂ) (b Z : ℝ)
  (h : Matches M H hH s η₀ θ w σ freq W b Z)

include h

theorem matches_prime_pool (j : Slot) :
    s.slots j = primePool M H b (s.P j) := by
  rw [h.pool,h.scale]

theorem matches_character_on_pool (j : Slot) (I : Ideal O) (hI : I ∈ s.slots j) :
    s.ν j I = idealCoeff η₀.inverse I := by
  rw [h.character]
  exact CenteredMomentDetectorPlainRelativeClass.relative_pool M H hH η₀ (θ j) b
    (s.P j) I ((matches_prime_pool M H hH s η₀ θ w σ freq W b Z h j) ▸ hI)

theorem matches_shifted_profiles :
    s.W = shiftedPrimeProfiles (fun _ : Slot => W) σ freq := by
  funext j y
  exact h.profile j y

theorem matches_annular_coefficient_on_pool
    (j : Slot) (I : Ideal O) (hI : I ∈ s.slots j) :
    s.ν j I*s.W j ((I.absNorm : ℝ)/s.P j) =
      idealCoeff η₀.inverse I*annularWeight W (s.P j) (σ j) (freq j) I := by
  rw [matches_character_on_pool M H hH s η₀ θ w σ freq W b Z h j I hI,h.profile]
  rfl

theorem matches_high_slot_gates :
    (∀ j, s.slots j = primePool M H b (s.P j)) ∧
    (∀ j I, I ∈ s.slots j → s.ν j I = idealCoeff η₀.inverse I) ∧
    (∀ j, s.W j = shiftedPrimeProfiles (fun _ : Slot => W) σ freq j) := by
  exact ⟨matches_prime_pool M H hH s η₀ θ w σ freq W b Z h,
    matches_character_on_pool M H hH s η₀ θ w σ freq W b Z h,
    fun j => congrFun (matches_shifted_profiles M H hH s η₀ θ w σ freq W b Z h) j⟩

#print axioms matches_high_slot_gates
#print axioms matches_annular_coefficient_on_pool
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointMatchesSlotGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointRetainedFiberMass ; sha256 3d6248f738eac7b70bdd4a6067a3bab63d2568f799b982d95e8d171e9c32a6b6 -/
section



/-! The complete retained fiber includes the second projector, both
common allocations, both active allocations and all four X/Y choices. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O

theorem secondCommonProfileScalar_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (η : Character) (A : O) (t : ℝ) :
    secondProfileScalar (secondCommonData s C R B η A t) ≤ secondProfileScalar s.toData := by
  unfold secondProfileScalar
  change Real.sqrt (2*(max 1 s.b₁*max 1 s.b₂)) *
      (∏ i : CenteredMomentCommonProfile.liveIndices B.val, s.M i.val) ≤ _
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [Finset.prod_coe_sort]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _ => zero_le_one.trans (s.M_ge_one i)) (fun i _ _ => s.M_ge_one i)

namespace CommonSecondKernelLabel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def withProjector (s : CommonSecondKernelLabel ι) (L : Ideal O) : CommonSecondKernelLabel ι :=
  {s with projector := L}

def fullFiberMass (s : CommonSecondKernelLabel ι) (Ds : Finset (Ideal O))
    (t₁ t₂ H₁ H₂ : ℝ) : ℝ :=
  ∑ L ∈ Ds, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
    ∑ q ∈ (s.withProjector L).retainedFiber t₁ t₂,
      (s.withProjector L).fiberWeight t₁ t₂ H₁ H₂ q

theorem fullFiberMass_eq (s : CommonSecondKernelLabel ι) (Ds : Finset (Ideal O))
    (t₁ t₂ H₁ H₂ : ℝ) :
    s.fullFiberMass Ds t₁ t₂ H₁ H₂ =
      4*∑ B : s.LeftAllocation, ∑ F : s.RightAllocation,
        (‖s.leftWeight B H₁‖*‖s.rightWeight F H₂‖)*
          (∑ L ∈ Ds, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
            ∑ a ∈ (s.leftData B t₁).toSource.active L,
              ∑ b ∈ (s.rightData F t₂).toSource.active L,
                secondAllocationScalar (s.leftData B t₁) (s.rightData F t₂) L a b) := by
  unfold fullFiberMass retainedFiber fiberWeight
  simp only [Finset.sum_sigma, Fintype.sum_bool]
  change (∑ L ∈ Ds, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
    ∑ B : s.LeftAllocation, ∑ F : s.RightAllocation,
      ∑ a ∈ (s.leftData B t₁).toSource.active L,
        ∑ b ∈ (s.rightData F t₂).toSource.active L,
          ((‖s.leftWeight B H₁‖*‖s.rightWeight F H₂‖)*
            secondAllocationScalar (s.leftData B t₁) (s.rightData F t₂) L a b+
           (‖s.leftWeight B H₁‖*‖s.rightWeight F H₂‖)*
            secondAllocationScalar (s.leftData B t₁) (s.rightData F t₂) L a b+
           ((‖s.leftWeight B H₁‖*‖s.rightWeight F H₂‖)*
            secondAllocationScalar (s.leftData B t₁) (s.rightData F t₂) L a b+
           (‖s.leftWeight B H₁‖*‖s.rightWeight F H₂‖)*
            secondAllocationScalar (s.leftData B t₁) (s.rightData F t₂) L a b))) = _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F hF
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end CommonSecondKernelLabel

theorem actual_retained_fiber_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι → ℝ) (Bcap δ : ℝ) (hBcap : 0 ≤ Bcap) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : CommonSecondKernelLabel ι), (∀ i, s.input.lo i = lo i) →
      (∀ i, s.input.hi i = hi i) → ∀ (Ds : Finset (Ideal O)),
      (∀ L ∈ Ds, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 → (L.absNorm : ℝ) ≤ Z^Bcap) →
      ∀ t₁ t₂ H₁ H₂ : ℝ,
      s.fullFiberMass Ds t₁ t₂ H₁ H₂ ≤
        4*C*Z^δ*(secondProfileScalar s.input.toData)^2 *
          ((∑ B : s.LeftAllocation, ‖s.leftWeight B H₁‖)*
            (∑ F : s.RightAllocation, ‖s.rightWeight F H₂‖)) := by
  obtain ⟨C,hC,hmass⟩ := actual_second_scalar_mass lo hi Bcap δ hBcap hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hslo hshi Ds hcap t₁ t₂ H₁ H₂
  rw [s.fullFiberMass_eq]
  have hprof := secondProfileScalar_nonneg s.input.toData
  have hpair (B : s.LeftAllocation) (F : s.RightAllocation) :
      secondProfileScalar (s.leftData B t₁)*secondProfileScalar (s.rightData F t₂) ≤
        (secondProfileScalar s.input.toData)^2 := by
    simpa only [CommonSecondKernelLabel.leftData, CommonSecondKernelLabel.rightData, pow_two] using mul_le_mul
      (secondCommonProfileScalar_le s.input _ _ B _ _ t₁)
      (secondCommonProfileScalar_le s.input _ _ F _ _ t₂)
      (secondProfileScalar_nonneg _) hprof
  calc
    _ ≤ 4*∑ B : s.LeftAllocation, ∑ F : s.RightAllocation,
        (‖s.leftWeight B H₁‖*‖s.rightWeight F H₂‖)*
          (C*Z^δ*(secondProfileScalar s.input.toData)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro B hB
      apply Finset.sum_le_sum
      intro F hF
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      exact (hZ.2 _ _ (s.leftData B t₁) (s.rightData F t₂)
        (fun i => hslo i.val) (fun i => hshi i.val)
        (fun i => hslo i.val) (fun i => hshi i.val) Ds hcap).trans
          (mul_le_mul_of_nonneg_left (hpair B F)
            (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hZ.1.le) _)))
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro F hF
      apply Finset.sum_congr rfl
      intro B hB
      ring

/-- All allocation and second-projector mass is subpower, with constants
chosen before the common ideals, physical dyads and source geometry. -/
theorem actual_complete_retained_fiber_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι → ℝ) (Bcap loss : ℝ) (hBcap : 0 ≤ Bcap) (hloss : 0 < loss) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : CommonSecondKernelLabel ι), (∀ i, s.input.lo i = lo i) →
      (∀ i, s.input.hi i = hi i) →
      ((s.firstCommon*s.second.val.1).absNorm : ℝ) ≤ Z^Bcap →
      ((s.firstCommon*s.second.val.2).absNorm : ℝ) ≤ Z^Bcap →
      ∀ (Ds : Finset (Ideal O)),
      (∀ L ∈ Ds, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 → (L.absNorm : ℝ) ≤ Z^Bcap) →
      ∀ (t₁ t₂ H₁ H₂ a : ℝ), 0 < a → 0 < H₁ → 0 < H₂ →
      a*CenteredMomentExceptionalAmplitudePair.volume s.input.toData/
        ((s.firstCommon*s.second.val.1).absNorm : ℝ) ≤ H₁ →
      a*CenteredMomentExceptionalAmplitudePair.volume s.input.toData/
        ((s.firstCommon*s.second.val.2).absNorm : ℝ) ≤ H₂ →
      s.fullFiberMass Ds t₁ t₂ H₁ H₂ ≤
        C*Z^loss*((secondProfileScalar s.input.toData)^2*commonSourceProfile s.input/a) := by
  obtain ⟨Cs,hCs,hsecond⟩ := actual_retained_fiber_mass lo hi Bcap (loss/2) hBcap (by positivity)
  obtain ⟨K,hK,hcommon⟩ := actual_common_fiber_mass (ι := ι) Bcap (loss/4) hBcap (by positivity)
  refine ⟨4*Cs*K^2,by positivity,?_⟩
  filter_upwards [hsecond] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hslo hshi hCcap hDcap Ds hLcap t₁ t₂ H₁ H₂ a ha hH₁ hH₂ hlower hrLower
  have hleft := hcommon Z hZ.1.le s.input (s.firstCommon*s.second.val.1) s.puncture
    (mul_ne_zero s.hfirst.1 s.toKernelLabel.hC.1) hCcap a H₁ ha hH₁ hlower
  have hright := hcommon Z hZ.1.le s.input (s.firstCommon*s.second.val.2) s.puncture
    (mul_ne_zero s.hfirst.1 s.toKernelLabel.hD.1) hDcap a H₂ ha hH₂ hrLower
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have hsc : 0 ≤ commonSourceProfile s.input/a :=
    div_nonneg (commonSourceProfile_nonneg s.input) ha.le
  have hp : Z^(loss/2)*(Z^(loss/4))^2 = Z^loss := by
    rw [pow_two, ← Real.rpow_add hZpos, ← Real.rpow_add hZpos]
    congr 1
    ring
  calc
    _ ≤ 4*Cs*Z^(loss/2)*(secondProfileScalar s.input.toData)^2 *
        ((∑ B : s.LeftAllocation, ‖s.leftWeight B H₁‖)*
          (∑ F : s.RightAllocation, ‖s.rightWeight F H₂‖)) :=
      hZ.2 s hslo hshi Ds hLcap t₁ t₂ H₁ H₂
    _ ≤ 4*Cs*Z^(loss/2)*(secondProfileScalar s.input.toData)^2 *
        ((K*Z^(loss/4)*Real.sqrt (commonSourceProfile s.input/a))^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [CommonSecondKernelLabel.leftWeight, CommonSecondKernelLabel.rightWeight, pow_two] using
        mul_le_mul hleft hright (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = (4*Cs*K^2)*Z^loss*((secondProfileScalar s.input.toData)^2*commonSourceProfile s.input/a) := by
      rw [mul_pow, Real.sq_sqrt hsc, mul_pow]
      calc
        _ = (4*Cs*K^2)*(Z^(loss/2)*(Z^(loss/4))^2)*
            ((secondProfileScalar s.input.toData)^2*commonSourceProfile s.input/a) := by ring
        _ = _ := by rw [hp]

#print axioms actual_retained_fiber_mass
#print axioms actual_complete_retained_fiber_mass
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointRetainedFiberMass -/
