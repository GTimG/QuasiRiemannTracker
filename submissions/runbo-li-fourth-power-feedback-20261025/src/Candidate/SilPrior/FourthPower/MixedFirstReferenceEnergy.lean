/- Copyright (c) 2026 Sil. Apache-2.0.
Actual selected-character reference energy with compact radial support.
Uniform controls are chosen for every subset of the original slot type
before the source, its Schwartz profiles, heights and scale are supplied.

-/
import Candidate.SilPrior.FourthPower.ReferenceUniformRestricted
import Candidate.SilPrior.FourthPower.MixedFirstReferenceDispatch
import Candidate.SilPrior.FourthPower.MixedFirstReferenceProfileBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstReferenceEnergy
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CompletedGauss (primaryGenerator)
open QRH.Record1252270103KernelMass
open CenteredMomentLattice CenteredMomentSourceProfileMass CenteredMomentScaleSupremum
open CenteredMomentFiniteProfileExceptional CenteredMomentOriginalRadialComparison
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredExceptionalProfile ReferencePrimeEnclosure
open MixedPrincipalPair MixedCommonHeights MixedFirstReferenceDispatch
open MixedFirstPuncturedReference MixedCanonicalSource ReferenceHeckeProducts
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

/-- The actual compact-profile supremum control, with no division by a
profile seminorm and therefore including the zero profile. -/
def radialControl (Φ : 𝓢(ℝ,ℂ)) : ℝ := sourceControl {(0,0)} Φ

theorem radial_control_nonneg (Φ : 𝓢(ℝ,ℂ)) : 0 ≤ radialControl Φ :=
  sourceControl_nonneg _ _

theorem real_profile_le (Φ : 𝓢(ℝ,ℂ)) (x : ℝ) : (Φ x).re ≤ radialControl Φ := by
  have hp : ‖Φ x‖ ≤ radialControl Φ := by
    simpa only [radialControl,sourceControl,Finset.sup_singleton,schwartzSeminormFamily]
      using SchwartzMap.norm_le_seminorm ℝ Φ x
  exact (Complex.re_le_norm _).trans hp

def keptRows (M : ℝ) (keep : O → Prop) : Finset O :=
  (rowNormDisk ⌊M⌋₊).filter keep

theorem mem_kept_rows (M : ℝ) (hM : 0 ≤ M) (keep : O → Prop) (z : O) :
    z ∈ keptRows M keep ↔ z ≠ 0 ∧ ‖eisEmbedding z‖^2 ≤ M ∧ keep z := by
  simp only [keptRows,Finset.mem_filter,TruncatedPrincipalPoisson.mem_rowNormDisk_floor hM]
  tauto

/-- Compact radial support produces a literal finite sum. This step
keeps the original F-dependent row restriction, including eligibility. -/
theorem radial_energy_le_finite (f : O → ℂ) (keep : O → Prop)
    (hkeep : ∀ z, keep z → z ≠ 0) (Φ : 𝓢(ℝ,ℂ)) (K bΦ M : ℝ)
    (hK : 0 < K) (hM : 0 ≤ M)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Iic bΦ) (hcap : bΦ*K ≤ M) :
    radialEnergy f keep Φ K ≤ radialControl Φ * ∑ z : keptRows M keep, ‖f z‖^2 := by
  have hzero (z : O) (hz : z ∉ keptRows M keep) :
      (if keep z then ‖f z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0) = 0 := by
    by_cases hk : keep z
    · have hp : Φ (‖eisEmbedding z‖^2/K) = 0 := by
        by_contra hn
        apply hz
        exact (mem_kept_rows M hM keep z).mpr
          ⟨hkeep z hk,((div_le_iff₀ hK).mp (hs hn)).trans hcap,hk⟩
      simp only [hk,ite_true,hp,Complex.zero_re,mul_zero]
    · simp only [hk,ite_false]
  have he : radialEnergy f keep Φ K =
      ∑ z : keptRows M keep, ‖f z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re := by
    unfold radialEnergy
    rw [tsum_eq_sum hzero]
    rw [Finset.sum_coe_sort (keptRows M keep)
      (fun z : O => ‖f z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re)]
    apply Finset.sum_congr rfl
    intro z hz
    rw [if_pos ((mem_kept_rows M hM keep z).mp hz).2.2]
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (real_profile_le Φ (‖eisEmbedding z‖^2/K)) (sq_nonneg ‖f z‖)

/-- Linear selected-character conductor factor. The coefficient puncture
Rmask is deliberately absent; if it remains inside m it is paid here.
The later sharp application uses the separately checked mask transport. -/
def conductorFactor (η : Character) (m : O) (F : Id) : ℝ :=
  (ReferenceCubicCharacter.conductorConstant : ℝ)*(η.modulus.absNorm : ℝ)*
    ((Ideal.span {m}).absNorm : ℝ)*((Ideal.span {(72 : O)}).absNorm : ℝ)*(F.absNorm : ℝ)

theorem conductor_factor_nonneg (η : Character) (m : O) (F : Id) :
    0 ≤ conductorFactor η m F := by
  unfold conductorFactor
  positivity

theorem selected_supported (η : Character) (m : O) (F : Id)
    (hm : m ≠ 0) (hF : Supported F) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (z : O) (hz : z ≠ 0) (I : Id) (hI : Supported I) :
    idealCoeff (selectedCharacterAt η m F hm hF hmLam hm2 z) I =
      fixedCoefficient η m (primaryGenerator F) I * idealRowHom z I := by
  rw [selectedCharacterAt,dif_pos hz]
  exact (Classical.choice (selected_character_exists η m F z hm hF hz hmLam hm2)).on_supported I hI

theorem selected_unsupported (η : Character) (m : O) (F : Id)
    (hm : m ≠ 0) (hF : Supported F) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (z : O) (hz : z ≠ 0) (I : Id) (hI : ¬Supported I) :
    idealCoeff (selectedCharacterAt η m F hm hF hmLam hm2 z) I = 0 := by
  rw [selectedCharacterAt,dif_pos hz]
  exact (Classical.choice (selected_character_exists η m F z hm hF hz hmLam hm2)).off_supported I hI

theorem selected_modulus (η : Character) (m : O) (F : Id)
    (hm : m ≠ 0) (hF : Supported F) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (z : O) (hz : z ≠ 0) :
    ((selectedCharacterAt η m F hm hF hmLam hm2 z).modulus.absNorm : ℝ) ≤
      conductorFactor η m F * ((Ideal.span {z}).absNorm : ℝ) := by
  rw [selectedCharacterAt,dif_pos hz]
  unfold conductorFactor
  exact_mod_cast
    (Classical.choice (selected_character_exists η m F z hm hF hz hmLam hm2)).modulus_bound

/-- The homogeneous short estimate applied to the actual selected
character and the exact height-shifted source rectangle. All constants
are uniform over T ⊆ ι, both original Schwartz profiles, Z, sources and
heights. Only explicit geometric/support/coefficient caps remain.

The conductor cap includes its fixed factor. It is not inferred merely
from R ≤ inputWidth. In the sharp application d may be d_ref = d + ω,
while the physical mixed-moment d remains unchanged. -/
theorem uniform_reference_energy {ι : Type u} [Fintype ι]
    (ε L Kcap a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hKcap : 0 < Kcap) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
    ∃ n : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ (T : Finset ι) (s : Source T a b) (Z R Pexp sWidth d l δ : ℝ),
      1 ≤ Z → 0 ≤ R → 0 ≤ sWidth → 0 ≤ d → 0 ≤ l → 0 ≤ δ →
      Pexp+2*sWidth+4*d < R → R+(l+(R+d)/2+sWidth+2*δ) ≤ L →
      l+(R+d)/2+sWidth+2*δ ≤ (4/5)*R → R+d+2*l-Pexp+sWidth+2*δ ≤ R/2 →
      (b+4)*b*(2:ℝ)^Fintype.card T ≤ Z^δ → xi/2 ≤ δ →
      ∀ (η : Character) (m : O) (F Q : Id)
        (hm : m ≠ 0) (hF : Supported F) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m),
      ∀ (keep : O → Prop), (∀ z, keep z → z ≠ 0) →
      (∀ z, keep z → ¬FixedInducingRow η Q m ((primaryGenerator F)^2) z) →
      ∀ (U X₁ X₂ Height t t₀ Bshort : ℝ) (ν : T → Character) (R₀ : T → Finset Id),
      s.ν = slotCoefficient ν R₀ t₀ →
      1 ≤ U → U ≤ Z^Kcap → U ≤ Z^(R+d) →
      0 < X₁ → 0 < X₂ → X₁*X₂ = Z^Pexp → X₁ ≤ Z^l →
      0 ≤ Height → ‖(s.t₂+t)/(2*Real.pi)‖ ≤ Height →
      0 ≤ Bshort → (∀ (j : Fin 2) (x : ℝ), ‖scaleTest (s.W₁ : ℝ → ℂ) j x‖ ≤ Bshort) →
      ((s.Fhole*s.R).absNorm : ℝ) ≤ Z^Kcap →
      (∀ P ∈ s.S, (P.val.absNorm : ℝ) ≤ Z^Kcap) →
      (∀ I, Supported I → ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues s.S) →
      (∀ i I, I ∈ s.pool i →
        ‖slotCoefficient ν R₀ (t₀+t) i I*s.Wslot i (I.absNorm/s.P i)‖ ≤ Bf) →
      (∀ i P, P ∈ s.H → P.val ∈ R₀ i) →
      (∏ i, 2*s.P i) ≤ Z^L → b*X₁*(∏ i, 2*s.P i) ≤ Z^L →
      (∏ i, s.P i) ≤ Z^sWidth →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (K bΦ : ℝ), 0 < K → 0 ≤ bΦ →
      Function.support (Φ : ℝ → ℂ) ⊆ Iic bΦ → bΦ*K ≤ Z^R →
      conductorFactor η m F * (bΦ*K) ≤ U →
      radialEnergy (fun z => heightRectangle s ha
        (selectedCharacterAt η m F hm hF hmLam hm2 z) t X₁ X₂) keep Φ K ≤
        radialControl Φ * (C*(sourceControl control s.W₂)^2*
          (1+Height)^(2*n)*Z^(R+ε)*Bshort^2) := by
  choose nT controlT CT hCT h00T hbound using fun T : Finset ι =>
    ReferenceUniformRestricted.short_actual_reference (ι := T)
      ε L Kcap a b xi Bf hε hL hKcap ha hb hxi hBf
  let n := ∑ T : Finset ι, nT T
  have hn (T : Finset ι) : nT T ≤ n :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ T)
  let control := (Finset.univ : Finset (Finset ι)).biUnion controlT
  have hcontrol (T : Finset ι) : controlT T ⊆ control :=
    Finset.subset_biUnion_of_mem controlT (Finset.mem_univ T)
  let C := 1+∑ T : Finset ι, CT T
  have hC : 0 < C := by
    have hh := Finset.sum_nonneg (fun T (_ : T ∈ (Finset.univ : Finset (Finset ι))) => (hCT T).le)
    dsimp [C]
    linarith
  have hCTC (T : Finset ι) : CT T ≤ C := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := CT)
      (fun T _ => (hCT T).le) (Finset.mem_univ T)
    dsimp [C]
    linarith
  refine ⟨n,control,C,hC,hcontrol ∅ (h00T ∅),?_⟩
  intro T s Z R Pexp sWidth d l δ hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m F Q hm hF hmLam hm2 keep hkeep heligible
    U X₁ X₂ Height t t₀ Bshort ν R₀ hν hU hUcap hUsharp
    hX₁ hX₂ hprod hshort hHeight ht₂ hBshort htest hholes hS henclose
    hβ hHR hVcap hvolume hVsharp Φ K bΦ hK hbΦ hΦ hradial hconductor
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hM : 0 ≤ bΦ*K := mul_nonneg hbΦ hK.le
  let rows := keptRows (bΦ*K) keep
  let χ (z : rows) : Character := selectedCharacterAt η m F hm hF hmLam hm2 z.val
  have hrows (z : rows) : z.val ≠ 0 ∧
      ‖eisEmbedding z.val‖^2 ≤ bΦ*K ∧ keep z.val :=
    (mem_kept_rows (bΦ*K) hM keep z.val).mp z.property
  have hactualNorm (z : O) (hz : z ∈ rows) :
      ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ*K := by
    rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact ((mem_kept_rows (bΦ*K) hM keep z).mp hz).2.1
  have hrowNorm (z : O) (hz : z ∈ rows) :
      ((Ideal.span {z}).absNorm : ℝ) ≤ Z^R := (hactualNorm z hz).trans hradial
  have hon (z : rows) (I : Id) (hI : Supported I) :
      idealCoeff (χ z) I = fixedCoefficient η m (primaryGenerator F) I*idealRowHom z.val I :=
    selected_supported η m F hm hF hmLam hm2 z.val (hrows z).1 I hI
  have hoff (z : rows) (I : Id) (hI : ¬Supported I) : idealCoeff (χ z) I = 0 :=
    selected_unsupported η m F hm hF hmLam hm2 z.val (hrows z).1 I hI
  have hnonprincipal (z : rows) : (χ z).residue ≠ 1 :=
    selected_character_at_nonprincipal η m F hm hF hmLam hm2 z.val (hrows z).1 Q
      (heligible z.val (hrows z).2.2)
  have hmod (z : rows) : ((χ z).modulus.absNorm : ℝ) ≤ U :=
    (selected_modulus η m F hm hF hmLam hm2 z.val (hrows z).1).trans
      ((mul_le_mul_of_nonneg_left (hactualNorm z.val z.property)
        (conductor_factor_nonneg η m F)).trans hconductor)
  have hfinite := hbound T s.W₂ s.hs₂ Z R Pexp sWidth d l δ
    hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m (primaryGenerator F) rows χ hon hoff hrowNorm hnonprincipal
    U X₁ X₂ Height ((s.t₁+t)/(2*Real.pi)) ((s.t₂+t)/(2*Real.pi)) s.W₁ Bshort
    hU hUcap hUsharp hX₁ hX₂ hprod hshort hHeight ht₂ hmod hBshort s.hs₁ (s.W₁.smooth ⊤) htest
    s.S s.H s.R s.Fhole s.hR s.hFhole hholes s.hH (fun P hP => ⟨s.hS P hP,hS P hP⟩)
    henclose s.pool ν R₀ (t₀+t) s.Wslot s.P s.hpool s.hp
    (fun i => zero_lt_one.trans_le (s.hP i)) s.hpn hβ hHR hVcap hvolume hVsharp
  have hnorm (z : rows) : ‖heightRectangle s ha (χ z) t X₁ X₂‖ =
      ‖rectangleRow (χ z) s.S s.H s.R s.pool (slotCoefficient ν R₀ (t₀+t)) s.Wslot s.P
        (phaseProfile s.W₁ ((s.t₁+t)/(2*Real.pi)))
        (phaseProfile s.W₂ ((s.t₂+t)/(2*Real.pi))) b X₁ X₂‖ := by
    rw [height_rectangle_canonical s ha ν R₀ t₀ hν (χ z) t X₁ X₂,norm_mul,
      residual_phase_norm (s.X₁*s.X₂)
        (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)) s.d s.hd 1 one_ne_zero t,one_mul]
  have hfiniteHeight : (∑ z : rows, ‖heightRectangle s ha (χ z) t X₁ X₂‖^2) ≤
      CT T*(sourceControl (controlT T) s.W₂)^2*(1+Height)^(2*nT T)*Z^(R+ε)*Bshort^2 := by
    simpa only [hnorm] using hfinite
  have hprofile : sourceControl (controlT T) s.W₂ ≤ sourceControl control s.W₂ :=
    Seminorm.le_def.mp (Finset.sup_mono (hcontrol T)) s.W₂
  have hcp : CT T*(sourceControl (controlT T) s.W₂)^2 ≤
      C*(sourceControl control s.W₂)^2 :=
    mul_le_mul (hCTC T)
      (pow_le_pow_left₀ (sourceControl_nonneg _ _) hprofile 2) (sq_nonneg _) hC.le
  have hnpow : (1+Height)^(2*nT T) ≤ (1+Height)^(2*n) :=
    pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left 2 (hn T))
  have hcommon : CT T*(sourceControl (controlT T) s.W₂)^2*
      (1+Height)^(2*nT T)*Z^(R+ε)*Bshort^2 ≤
      C*(sourceControl control s.W₂)^2*(1+Height)^(2*n)*Z^(R+ε)*Bshort^2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul hcp hnpow (by positivity) (mul_nonneg hC.le (sq_nonneg _)))
        (Real.rpow_nonneg hZp.le _)) (sq_nonneg Bshort)
  apply (radial_energy_le_finite
    (fun z => heightRectangle s ha (selectedCharacterAt η m F hm hF hmLam hm2 z) t X₁ X₂)
    keep hkeep Φ K bΦ (bΦ*K) hK hM hΦ le_rfl).trans
  exact mul_le_mul_of_nonneg_left (hfiniteHeight.trans hcommon) (radial_control_nonneg Φ)

/-- The actual reference estimate with the profile and height inputs
discharged uniformly. Constants precede both original Schwartz profiles,
all live subsets, heights, selected twists and radial scales. The zero
profile remains homogeneous, and all geometric/conductor caps stay explicit.
-/
theorem uniform_profiled_reference_energy {ι : Type u} [Fintype ι]
    (ε L Kcap a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hKcap : 0 < Kcap) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ (T : Finset ι) (s : Source T a b) (Z R Pexp sWidth d l δ : ℝ),
      1 ≤ Z → 0 ≤ R → 0 ≤ sWidth → 0 ≤ d → 0 ≤ l → 0 ≤ δ →
      Pexp+2*sWidth+4*d < R → R+(l+(R+d)/2+sWidth+2*δ) ≤ L →
      l+(R+d)/2+sWidth+2*δ ≤ (4/5)*R → R+d+2*l-Pexp+sWidth+2*δ ≤ R/2 →
      (b+4)*b*(2:ℝ)^Fintype.card T ≤ Z^δ → xi/2 ≤ δ →
      ∀ (η : Character) (m : O) (F Q : Id)
        (hm : m ≠ 0) (hF : Supported F) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m),
      ∀ (keep : O → Prop), (∀ z, keep z → z ≠ 0) →
      (∀ z, keep z → ¬FixedInducingRow η Q m ((primaryGenerator F)^2) z) →
      ∀ (U X₁ X₂ t t₀ V : ℝ) (ν : T → Character) (R₀ : T → Finset Id),
      s.ν = slotCoefficient ν R₀ t₀ →
      1 ≤ U → U ≤ Z^Kcap → U ≤ Z^(R+d) →
      0 < X₁ → 0 < X₂ → X₁*X₂ = Z^Pexp → X₁ ≤ Z^l →
      0 ≤ V →
      ((s.Fhole*s.R).absNorm : ℝ) ≤ Z^Kcap →
      (∀ P ∈ s.S, (P.val.absNorm : ℝ) ≤ Z^Kcap) →
      (∀ I, Supported I → ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues s.S) →
      (∀ i I, I ∈ s.pool i →
        ‖slotCoefficient ν R₀ (t₀+t) i I*s.Wslot i (I.absNorm/s.P i)‖ ≤ Bf) →
      (∀ i P, P ∈ s.H → P.val ∈ R₀ i) →
      (∏ i, 2*s.P i) ≤ Z^L → b*X₁*(∏ i, 2*s.P i) ≤ Z^L →
      (∏ i, s.P i) ≤ Z^sWidth →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (K bΦ : ℝ), 0 < K → 0 ≤ bΦ →
      Function.support (Φ : ℝ → ℂ) ⊆ Iic bΦ → bΦ*K ≤ Z^R →
      conductorFactor η m F * (bΦ*K) ≤ U →
      radialEnergy (fun z => heightRectangle s ha
        (selectedCharacterAt η m F hm hF hmLam hm2 z) t X₁ X₂) keep Φ K ≤
        radialControl Φ * (C*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
          (MixedFirstProfileEnvelope.height t V s.t₁ s.t₂)^J*Z^(R+ε)) := by
  obtain ⟨n,Sref,Cref,hCref,h00ref,href⟩ := uniform_reference_energy (ι := ι)
    ε L Kcap a b xi Bf hε hL hKcap ha hb hxi hBf
  obtain ⟨control,J,Cp,D,hCp,hD,hsub,h00,hprofiles⟩ :=
    MixedFirstReferenceProfileBudget.uniform_profile_controls a b ha Sref ∅ n
  refine ⟨J,control,Cref*Cp,mul_pos hCref hCp,h00,?_⟩
  intro T s Z R Pexp sWidth d l δ hZ hR hs hd hl hδ hcap htotal hmax hlength hfixed hξ
    η m F Q hm hF hmLam hm2 keep hkeep heligible
    U X₁ X₂ t t₀ V ν R₀ hν hU hUcap hUsharp
    hX₁ hX₂ hprod hshort hV hholes hS henclose
    hβ hHR hVcap hvolume hVsharp Φ K bΦ hK hbΦ hΦ hradial hconductor
  let Height := |t|+‖s.t₁‖+‖s.t₂‖
  let Bshort := D*sourceControl control s.W₁
  have hheight := MixedFirstReferenceProfileBudget.shifted_reference_height t V s.t₁ s.t₂ hV
  have hp := hprofiles s.W₁ s.W₂ s.hs₁ s.hs₂ t V s.t₁ s.t₂ hV
  have hBshort : 0 ≤ Bshort := mul_nonneg hD.le (sourceControl_nonneg _ _)
  have he := href T s Z R Pexp sWidth d l δ hZ hR hs hd hl hδ hcap htotal hmax
    hlength hfixed hξ η m F Q hm hF hmLam hm2 keep hkeep heligible
    U X₁ X₂ Height t t₀ Bshort ν R₀ hν hU hUcap hUsharp hX₁ hX₂ hprod hshort
    hheight.1 hheight.2.2.1 hBshort hp.1 hholes hS henclose hβ hHR hVcap hvolume hVsharp
    Φ K bΦ hK hbΦ hΦ hradial hconductor
  have hpay := hp.2.2.2.1
  have hz := Real.rpow_nonneg (zero_le_one.trans hZ) (R+ε)
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (radial_control_nonneg Φ)
  calc
    Cref*(sourceControl Sref s.W₂)^2*(1+Height)^(2*n)*Z^(R+ε)*Bshort^2 =
        Cref*((sourceControl Sref s.W₂)^2*(1+Height)^(2*n)*Bshort^2)*Z^(R+ε) := by ring
    _ ≤ Cref*(Cp*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (MixedFirstProfileEnvelope.height t V s.t₁ s.t₂)^J)*Z^(R+ε) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpay hCref.le) hz
    _ = _ := by ring

end
end Candidate.SilPrior.FourthPower.MixedFirstReferenceEnergy
