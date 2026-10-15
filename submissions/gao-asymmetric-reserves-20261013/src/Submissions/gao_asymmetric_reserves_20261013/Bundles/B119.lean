/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below.
Affine-capacity adaptation: the source module hashes below identify the
pre-adaptation provenance, not the modified declarations in this file. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B112
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B118
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.InductionEnergy

/- BEGIN ORIGINAL MODULE Analytic.JointFirstHeightExtension ; sha256 5b2ed24e08226f32b6449bf2ef8baeef9c5a7e7aec16eb7e4f3b51d709ae93b8 -/
section



/-! The elementary absolute estimate is uniform in both Fourier heights
and all row masks. It supplies the large-height branch of the local moment. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy CenteredMomentEnergyReferenceState
open CenteredMomentCommonRadialData CenteredMomentSourceRow CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentEnergyNaturalInputMatches CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

/-- A fixed height degree absorbs any fixed excess power above the target. -/
theorem large_height_absorbs_power (ν K target : ℝ) (hν : 0 < ν) :
    ∃ J : ℕ, ∀ Z H : ℝ,1 ≤ Z → Z^ν < H →
      Z^K ≤ Z^target*(1+H)^J := by
  obtain ⟨J,hJ⟩ := exists_nat_gt ((K-target)/ν)
  have hbudget : K ≤ target+ν*(J:ℝ) := by
    have hh := (div_lt_iff₀ hν).mp hJ
    nlinarith
  refine ⟨J,?_⟩
  intro Z H hZ hH
  have hz := zero_lt_one.trans_le hZ
  calc
    _ ≤ Z^(target+ν*(J:ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hbudget
    _ = Z^target*(Z^ν)^J := by rw [Real.rpow_add hz,Real.rpow_mul hz.le,Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hz.le _) (by linarith) J) (by positivity)

/-- The two bounded coordinates are extended at once. The degree and
constant are fixed before the base or heights are chosen. -/
theorem all_height_bound_of_local_and_coarse (ν ε C₀ C₁ : ℝ) (J₀ : ℕ)
    (hν : 0 < ν) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) :
    ∃ J : ℕ, ∀ Z t height E : ℝ,1 ≤ Z → 0 ≤ height →
      E ≤ C₀*Z^(2:ℝ) →
      (|t| ≤ Z^ν → height ≤ Z^ν → E ≤ C₁*(1+|t|+height)^J₀*Z^(1+ε)) →
      E ≤ (C₀+C₁)*(1+|t|+height)^J*Z^(1+ε) := by
  obtain ⟨J₁,hlarge⟩ := large_height_absorbs_power ν 2 (1+ε) hν
  refine ⟨max J₀ J₁,?_⟩
  intro Z t height E hZ hheight hcoarse hlocal
  have hbase : 1 ≤ 1+|t|+height := by linarith [abs_nonneg t]
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  by_cases ht : |t| ≤ Z^ν
  · by_cases hh : height ≤ Z^ν
    · apply (hlocal ht hh).trans
      have hpow := pow_le_pow_right₀ hbase (Nat.le_max_left J₀ J₁)
      gcongr <;> linarith
    · have hh' : Z^ν < |t|+height := by linarith [abs_nonneg t]
      have hp := hlarge Z (|t|+height) hZ hh'
      have hpow := pow_le_pow_right₀ hbase (Nat.le_max_right J₀ J₁)
      calc
        E ≤ C₀*Z^(2:ℝ) := hcoarse
        _ ≤ C₀*(Z^(1+ε)*(1+(|t|+height))^J₁) := mul_le_mul_of_nonneg_left hp hC₀
        _ = C₀*(1+|t|+height)^J₁*Z^(1+ε) := by ring
        _ ≤ _ := by gcongr <;> linarith
  · have hh' : Z^ν < |t|+height := by linarith
    have hp := hlarge Z (|t|+height) hZ hh'
    have hpow := pow_le_pow_right₀ hbase (Nat.le_max_right J₀ J₁)
    calc
      E ≤ C₀*Z^(2:ℝ) := hcoarse
      _ ≤ C₀*(Z^(1+ε)*(1+(|t|+height))^J₁) := mul_le_mul_of_nonneg_left hp hC₀
      _ = C₀*(1+|t|+height)^J₁*Z^(1+ε) := by ring
      _ ≤ _ := by gcongr <;> linarith

 def firstNaturalCoarseConstant (N : ℕ) (M U b B₁ B₂ : ℝ) : ℝ :=
  ((128*b*B₁)*(128*b*B₂)*(128*max 1 U*M)^N)^2

theorem actual_input_coarse_energy {α : Type*} [Fintype α] [DecidableEq α]
    (src : Input α) (m A : O) (t Z K M U b B₁ B₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ))
    (hZ : 1 ≤ Z) (hK : 0 < K) (hKcap : K ≤ Z)
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hMs : ∀ i,src.M i ≤ M) (hU : src.upper ≤ U)
    (hb₁ : src.b₁ ≤ b) (hb₂ : src.b₂ ≤ b)
    (hW₁ : ∀ x,‖src.W₁ x‖ ≤ B₁) (hW₂ : ∀ x,‖src.W₂ x‖ ≤ B₂)
    (hvolume : volume src.toData ≤ Z) :
    energy src.η m A t src.W₁ src.W₂ src.slots src.toData.coefficient src.P src.X₁ src.X₂ keep Φ K ≤
      (diagonalControl Φ*firstNaturalCoarseConstant (Fintype.card α) M U b B₁ B₂)*Z^(2:ℝ) := by
  have hcoeff (i) (I) (hI : I∈src.slots i) : ‖src.toData.coefficient i I‖ ≤ M :=
    (src.coefficient_bound i I hI).trans (hMs i)
  have hnorm (i) (I) (_hI : I∈src.slots i) (hn : src.toData.coefficient i I ≠ 0) :
      (I.absNorm:ℝ) ≤ max 1 U*src.P i := by
    have hW : src.W i ((I.absNorm:ℝ)/src.P i) ≠ 0 := right_ne_zero_of_mul hn
    have hh := ((src.slot_support i hW).2.trans hU).trans (le_max_right 1 U)
    exact (div_le_iff₀ (src.P_pos i)).mp hh
  have hh := energy_absolute src.η m A t src.W₁ src.W₂ b b B₁ B₂ src.X₁ src.X₂
    hb hb hB₁ hB₂ src.X₁_pos src.X₂_pos
    (fun x hx=>(src.support₁ hx).trans hb₁) (fun x hx=>(src.support₂ hx).trans hb₂)
    hW₁ hW₂ src.slots src.toData.coefficient src.P (fun _=> max 1 U) (fun _=> M)
    src.P_pos (fun _=> by positivity) (fun _=> hM) hcoeff hnorm keep Φ K hK
  have hd := diagonalControl_nonneg Φ
  have hmax : max 1 K ≤ Z := max_le hZ hKcap
  have hv : 0 ≤ volume src.toData := (volume_pos src.toData).le
  simp only [Finset.prod_const,Finset.card_univ] at hh
  change energy _ _ _ _ _ _ _ _ _ _ _ _ _ _ ≤
    diagonalControl Φ*max 1 K*(firstNaturalCoarseConstant (Fintype.card α) M U b B₁ B₂*volume src.toData) at hh
  apply hh.trans
  calc
    _ ≤ diagonalControl Φ*Z*(firstNaturalCoarseConstant (Fintype.card α) M U b B₁ B₂*Z) := by
      unfold firstNaturalCoarseConstant
      gcongr
    _ = _ := by rw [Real.rpow_two];ring

namespace LocalFirstNaturalSource
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance naturalHeightFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Genuine coarse energy for the original natural source. The constant
is independent of the character, masks, all heights and all slot frequencies. -/
theorem actual_natural_coarse_energy
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi a b : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (ha : 0 < a) (hb : 0 ≤ b) (p : Profiles a b) (Φ : 𝓢(ℝ,ℂ)) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (Z Bmask bΦ : ℝ),1 < Z →
      ∀ (s : NaturalState Z Bmask bΦ),s.rowWidth=1 → s.radial.profile=Φ →
      ∀ (η₀ : Character) (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (hσ : ∀ i,σ i∈Set.Icc lo hi) (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂),
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 → (∑ i,w i) ≤ 37/1000 →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤ C*Z^(2:ℝ) := by
  let Mslot := profileBound W hW aslot bslot lo hi haslot hWs
  let B₁ := SchwartzMap.seminorm ℝ 0 0 (p.profile 0)
  let B₂ := SchwartzMap.seminorm ℝ 0 0 (p.profile 1)
  have hM : 0 ≤ Mslot := zero_le_one.trans (profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
  refine ⟨diagonalControl Φ*firstNaturalCoarseConstant (Fintype.card α) Mslot bslot b B₁ B₂,
    mul_nonneg (diagonalControl_nonneg Φ) (sq_nonneg _),?_⟩
  intro Z Bmask bΦ hZ s hrow hΦ η₀ θ w σ freq hσ t X₁ X₂ hX₁ hX₂ hn₁ hn₂ hw
  let src := input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂
  have hscale : s.radial.scale = Z := by rw [s.scale_eq,hrow,Real.rpow_one]
  have hvolume : volume src.toData ≤ Z := by
    have hlog := original_volume_log src Z w hZ (fun _=> rfl)
    have hcap : Real.logb Z (volume src.toData) ≤ 1 := by
      change Real.logb Z (volume src.toData) = Real.logb Z X₁+Real.logb Z X₂+∑ i,w i at hlog
      linarith only [hlog,hn₁,hn₂,hw]
    calc
      _ = Z^(Real.logb Z (volume src.toData)) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (volume_pos src.toData)).symm
      _ ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le hcap
      _ = _ := Real.rpow_one Z
  have hh := actual_input_coarse_energy src s.mask 1 t Z s.radial.scale Mslot bslot b B₁ B₂
    s.radial.keep Φ hZ.le s.radial.scale_pos hscale.le hM hb (by positivity) (by positivity)
    (fun _=> le_rfl) le_rfl le_rfl le_rfl (SchwartzMap.norm_le_seminorm ℝ _) (SchwartzMap.norm_le_seminorm ℝ _)
    hvolume
  have heq := original_energy M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂
  rw [←hΦ] at hh
  change energy src.η s.mask 1 src.t src.W₁ src.W₂ src.slots src.toData.coefficient src.P
    src.X₁ src.X₂ s.radial.keep s.radial.profile s.radial.scale ≤ _ at hh
  rw [heq] at hh
  simpa only [hΦ] using hh

end LocalFirstNaturalSource
#print axioms large_height_absorbs_power
#print axioms all_height_bound_of_local_and_coarse
#print axioms actual_input_coarse_energy
#print axioms LocalFirstNaturalSource.actual_natural_coarse_energy
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstHeightExtension -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstNaturalFromAnnular ; sha256 e26a81da278c7282b41009daae943a9f39db4f1ed8d4d7873fe167e45b6f42ba -/
section




/-! The original natural energy follows from the actual annular source
targets. Plain and radial profiles are fixed before the final constant;
all geometric, support and normalization gates are proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalSource CenteredMomentLogDyadic
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentEnergyNaturalInputMatches CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance naturalFromAnnularSumDecEq : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

/-- Only the genuine finite annular source target is assumed here. -/
def FirstNaturalAnnularTargets (src : Input α) (R : Ideal O) (Z ξ t : ℝ)
    (Wradial : 𝓢(ℝ,ℂ)) (e ηheight C : ℝ) : Prop :=
  let radius := actualLowFirstRadius src R 1 Z Z ξ
  let q := firstSourceOuterLabel src R 1 Z radius
  let live := firstLiveSourceLabels src R 1 Z radius Finset.univ (fun _ => t) Wradial (fun _ => logAnnulus)
  ∀ (labels : Finset (FirstSourceOuterIndex src R 1 Z radius)),labels ⊆ live →
    ∀ ref ∈ labels,
    (∀ i ∈ labels,∀ j,|(q i).fullWidthCoordinates Z j-(q ref).fullWidthCoordinates Z j| < e) →
    (∀ i ∈ labels,(q ref).activeWidth Z/2+(q ref).punctureWidth Z ≤
      (q i).activeWidth Z/2+(q i).punctureWidth Z) →
    ∀ u : Bool → ((i : FirstSourceOuterIndex src R 1 Z radius) × (q i).SourceIndex) → ℝ,
      (∀ left,∀ k ∈ firstSourceLabels labels q,|u left k| ≤ Z^ηheight) →
      ∀ left,
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).sideEnergy left (u left k) profile (dyadicScale (k.1.2.2 1))) ≤
        (volume src.toData/(((q ref).sideCommon left).absNorm : ℝ))*
          (C*Z^((q ref).sideTargetWidth left Z (Real.logb Z (volume src.toData))))

private theorem four_terms_height (a b c d X Y H : ℝ)
    (hX : 0 ≤ X) (hXY : X ≤ Y) (hH : 1 ≤ H) :
    a*X+b*Y+c*Y+d*H*Y ≤ (1+|a|+|b|+|c|+|d|)*H*Y := by
  have hY : 0 ≤ Y := hX.trans hXY
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have base (v : ℝ) : v*Y ≤ |v| *H*Y := by
    calc
      _ ≤ |v| *Y := mul_le_mul_of_nonneg_right (le_abs_self v) hY
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg v) hY]
  have ha : a*X ≤ |a| *H*Y := by
    calc
      _ ≤ |a| *X := mul_le_mul_of_nonneg_right (le_abs_self a) hX
      _ ≤ |a| *Y := mul_le_mul_of_nonneg_left hXY (abs_nonneg a)
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg a) hY]
  have hd : d*H*Y ≤ |d| *H*Y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self d) hH₀) hY
  nlinarith [base b,base c,mul_nonneg hH₀ hY]

variable (M : Ideal O) [NeZero M]
local instance naturalFromAnnularFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- For fixed plain and radial profiles, a uniform annular target gives
the original fourth-moment energy bound. The exact natural-state gates and
original coefficient family remain in the conclusion. -/
theorem actual_local_natural_from_annular
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Wslot : ℝ → ℂ) (aslot bslot lo hi a b bΦ Bmask ε ξ e : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hcSlot : ContDiff ℝ ∞ Wslot) (hbslot : 0 < bslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hε : 0 < ε) (hξ : 0 < ξ) (hξcap : ξ ≤ 1)
    (he : 0 < e) (heε : e ≤ ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ mesh : ℝ, 0 < mesh ∧ mesh ≤ lowLocalMesh ∧ ∃ J : ℕ,
    ∀ (ηfirst η₀ : Character) (Q : Ideal O), Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∀ (p : Profiles a b) (Wradial : 𝓢(ℝ,ℂ)) (ν ηheight CAnn : ℝ),
      0 < ν → ν < ηheight → 0 ≤ CAnn →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
    ∀ (hσlo : ∀ i,lo ≤ σ i) (hσhi : ∀ i,σ i ≤ hi),
      0 ≤ height → height ≤ Z^ν → (∀ i,|freq i| ≤ height) → |t| ≤ Z^ν →
    ∀ (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      410/1000 ≤ Real.logb Z X₁ → 410/1000 ≤ Real.logb Z X₂ →
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z X₁) (Real.logb Z X₂) (∑ i,w i) →
    ∀ s : NaturalState Z Bmask bΦ,
      s.fixedModulus = internalQ Q η₀ → s.character = ηfirst → s.rowWidth = 1 →
      s.characterWidth = Real.logb Z (ηfirst.modulus.absNorm : ℝ) → s.radial.profile = Wradial →
    let src := LocalFirstNaturalSource.input M H hH η₀ θ Wslot hcSlot.continuous
      aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩)
      s p ha t X₁ X₂ hX₁ hX₂;
    FirstNaturalAnnularTargets src s.puncture Z ξ t Wradial e ηheight CAnn →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        C*(1+|t|+height)^J*Z^(1+ε) := by
  obtain ⟨mesh₀,hmesh₀,J,U,Sd,St,Cd,Ct,hCd,hCt,hnatural⟩ :=
    actual_local_first_natural_target (α := α) M H hH Wslot aslot bslot lo hi a b bΦ Bmask ε ξ
      haslot hsSlot hcSlot hbslot ha hlo hhi hbΦ hBmask hε hξ hbeta hbetaTop
  have hmesh : 0 < lowLocalMesh := (low_local_parameter_choices (Fintype.card α)).1
  refine ⟨min mesh₀ lowLocalMesh,lt_min hmesh₀ hmesh,min_le_right _ _,J,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72 p Wradial ν ηheight CAnn hν hgap hAnn
  obtain ⟨Cc,hCc,hnatural⟩ := hnatural ηfirst η₀ Q hQM hQzero hQtop hQ72
  let B₁ := SchwartzMap.seminorm ℝ 0 0 (p.profile 0)
  let B₂ := SchwartzMap.seminorm ℝ 0 0 (p.profile 1)
  have hB₁ : 0 ≤ B₁ := apply_nonneg _ _
  have hB₂ : 0 ≤ B₂ := apply_nonneg _ _
  let F := profileBound Wslot hcSlot.continuous aslot bslot lo hi haslot hsSlot
  let lower := aslot^Fintype.card α*a^2
  have hlower : 0 < lower := by dsimp only [lower];positivity
  obtain ⟨Ca,hCa,habsolute⟩ := eventually_original_first_absolute_from_annular_targets
    (ι := α) Wradial (Fintype.card α) ν ηheight F bslot b b B₁ B₂ a a lower e 0 (883/1000)
    hν hgap hB₁ hB₂ ha.le ha.le hlower he
  let K := firstSourceCoarseConstant (Fintype.card α) F bslot b b B₁ B₂
    (diagonalControl profile)
  let Pplain := F^Fintype.card α*B₁*B₂
  let ca := 2*Ca*(CAnn+K)
  let cd := 2*Cd*Pplain^2*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wradial
  let ct := 2*Ct*Pplain^2*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wradial
  let cc := 2*Cc*diagonalControl Wradial*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2
  refine ⟨1+|ca|+|cd|+|ct|+|cc|,by positivity,?_⟩
  filter_upwards [hnatural,habsolute,
    LocalFirstNaturalSource.eventually_join_geometry (α := α) M H hH Wslot hcSlot.continuous
      aslot bslot lo hi a b haslot hbslot hsSlot ha hhi] with Z hnatural habsolute hgeometry
  refine ⟨hnatural.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hheight hheightCap hfreq ht
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial src hannular
  have hZ := hnatural.1
  have hz := zero_lt_one.trans hZ
  have hw₀ : ∀ i,w i ≤ mesh₀ := fun i => (hwmesh i).trans (min_le_left _ _)
  have hwlocal : ∀ i,w i ≤ lowLocalMesh := fun i => (hwmesh i).trans (min_le_right _ _)
  have hg := hgeometry.2 η₀ θ w σ freq (fun i => ⟨hσlo i,hσhi i⟩) Bmask bΦ s p
    t X₁ X₂ hX₁ hX₂ hw hwlocal hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity
  have hp := LocalFirstNaturalSource.plain_join_gates M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hlowerEq := LocalFirstNaturalSource.lower_profile_exact M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have haTarget := habsolute src s.puncture le_rfl (fun _ => le_rfl) le_rfl le_rfl le_rfl
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2
    (le_of_eq hlowerEq.symm) hg.source_positive (by simpa only [Real.rpow_one] using hg.source_cap)
    (Real.logb Z (volume src.toData)) hg.width_nonneg (hg.width_upper.trans (by norm_num)) hg.volume_eq
    ξ hξcap t CAnn ht hAnn
  have haBound := haTarget (by
    simpa only [FirstNaturalAnnularTargets,Real.rpow_logb hz hZ.ne' (volume_pos src.toData)] using hannular)
  have hpc := LocalFirstNaturalSource.plain_control M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hinitial := hnatural.2 θ w σ freq t height hw hw₀ hσlo hσhi hheight hfreq
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum s hQ hη hrow hwidth p
  change plainControl src (p.profile 0) (p.profile 1)=Pplain at hpc
  change energy _ _ _ _ _ _ _ _ _ _ _ _ _ _ ≤ _ at hinitial
  rw [hradial,hpc] at hinitial
  have hmain : (2/volume src.toData)*
      (∑ i : FirstSourceOuterIndex src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ),
        ‖firstPhysicalValue src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ)
          (fun _ => t) Wradial (fun _ => logAnnulus) i‖) ≤ ca*Z^(1+e) := by
    have hh := mul_le_mul_of_nonneg_left haBound (by norm_num : (0:ℝ) ≤ 2)
    convert hh using 1 <;> (try dsimp only [ca,K]) <;> ring
  have hH : 1 ≤ (1+|t|+height)^J := one_le_pow₀ (by linarith [abs_nonneg t])
  have hpow : Z^(1+e) ≤ Z^(1+ε) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hfour := four_terms_height ca cd ct cc (Z^(1+e)) (Z^(1+ε)) ((1+|t|+height)^J)
    (Real.rpow_nonneg hz.le _) hpow hH
  rw [hradial]
  apply hinitial.trans
  apply le_trans _ hfour
  dsimp only [cd,ct,cc]
  exact add_le_add (add_le_add (add_le_add hmain le_rfl) le_rfl) le_rfl

#print axioms actual_local_natural_from_annular
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstNaturalFromAnnular -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighDyadicGates ; sha256 d71b6bd8ab9cebb2625df77b4d1b71d3808521bd750703875ff034ca106bddf1 -/
section



/-! Actual dyadic source caps and the upper/lower first-sector scale
transport. The residual source radius and both original common ideals
supply all polynomial caps; no independent second-scale gate is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma firstLowMainScale_eq_exponent (q : FirstJointLabel ι) (side : Bool)
    (Z A M omega : ℝ) :
    firstLowMainScale q side Z A M omega =
      Z^(firstMainExponent A (q.sideWidth side Z) (q.sideWidth (!side) Z)
        (q.activeWidth Z) (q.punctureWidth Z) M (3/500) omega) := by
  unfold firstLowMainScale firstMainExponent
  rw [←q.activeWidth_normValue,←q.punctureWidth_normValue]
  rfl

lemma firstLowMainScale_sector_bounds (q ref : FirstJointLabel ι) (side : Bool)
    (Z A M omega e : ℝ) (hZ : 1 < Z) (he : 0 ≤ e)
    (hc : |q.sideWidth side Z-ref.sideWidth side Z| ≤ e)
    (hd : |q.sideWidth (!side) Z-ref.sideWidth (!side) Z| ≤ e)
    (hR : |q.activeWidth Z-ref.activeWidth Z| ≤ e)
    (hE : |q.punctureWidth Z-ref.punctureWidth Z| ≤ e) :
    firstLowMainScale q side Z A M omega ≤
      Z^(firstMainExponent A (ref.sideWidth side Z) (ref.sideWidth (!side) Z)
        (ref.activeWidth Z) (ref.punctureWidth Z) M (3/500) (omega+6*e)) ∧
    Z^(firstMainExponent A (ref.sideWidth side Z-e) (ref.sideWidth (!side) Z-e)
        (ref.activeWidth Z) (ref.punctureWidth Z) M (3/500) (omega-8*e)) ≤
      firstLowMainScale q side Z A M omega := by
  rw [firstLowMainScale_eq_exponent]
  constructor
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have hh := first_main_exponent_upper A (q.sideWidth side Z) (q.sideWidth (!side) Z)
      (q.activeWidth Z) (q.punctureWidth Z) (ref.sideWidth side Z) (ref.sideWidth (!side) Z)
      (ref.activeWidth Z) (ref.punctureWidth Z) M (3/500) omega e he hc hd hR hE
    simpa only [firstMainExponent,add_assoc] using hh
  · exact Real.rpow_le_rpow_of_exponent_le hZ.le
      (first_row_scale_sector_lower A (q.sideWidth side Z) (q.sideWidth (!side) Z)
        (q.activeWidth Z) (q.punctureWidth Z) (ref.sideWidth side Z) (ref.sideWidth (!side) Z)
        (ref.activeWidth Z) (ref.punctureWidth Z) M (3/500) omega e he hc hd hR hE)

lemma firstLowMainScale_ge_inv_cube (q : FirstJointLabel ι) (side : Bool)
    (Z A omega : ℝ) (hZ : 1 < Z) (hA : 0 ≤ A) (homega : 0 ≤ omega)
    (hC : (q.C.absNorm : ℝ) ≤ Z^(1:ℝ)) (hD : (q.D.absNorm : ℝ) ≤ Z^(1:ℝ)) :
    Z^(-3:ℝ) ≤ firstLowMainScale q side Z A 1 omega := by
  have hc := q.sideWidth_bounds side Z 1 hZ hC hD
  have hd := q.sideWidth_bounds (!side) Z 1 hZ hC hD
  have hn := q.target_auxiliary_widths_nonneg Z hZ
  rw [firstLowMainScale_eq_exponent]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  unfold firstMainExponent
  linarith [le_max_right (q.sideWidth (!side) Z-q.sideWidth side Z) 0]

lemma firstLowRadius_polynomial_cap (q : FirstJointLabel ι) (side : Bool)
    (Hsource Z A omega ξ : ℝ) (hZ : 1 < Z) (hA : 0 ≤ A) (homega : 0 ≤ omega)
    (hξ : ξ ≤ 1) (hH₀ : 0 ≤ Hsource) (hH : Hsource ≤ Z^(1:ℝ))
    (hC : (q.C.absNorm : ℝ) ≤ Z^(1:ℝ)) (hD : (q.D.absNorm : ℝ) ≤ Z^(1:ℝ)) :
    firstLowRadius q side Hsource Z A 1 omega ξ ≤ Z^(6:ℝ) := by
  have hz := zero_lt_one.trans hZ
  have hn : (1:ℝ) ≤ (q.sideCommon side).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (q.sideCommon_supported side).1)
  have hdiv : 0 ≤ Hsource/((q.sideCommon side).absNorm : ℝ) := by positivity
  have hdivcap : Hsource/((q.sideCommon side).absNorm : ℝ) ≤ Z^(1:ℝ) :=
    (div_le_self hH₀ hn).trans hH
  have hK := firstLowMainScale_ge_inv_cube q side Z A omega hZ hA homega hC hD
  change ((Hsource/((q.sideCommon side).absNorm : ℝ))^2 /
    firstLowMainScale q side Z A 1 omega)*Z^(ξ/2) ≤ _
  calc
    _ ≤ ((Z^(1:ℝ))^2/Z^(-3:ℝ))*Z^(ξ/2) := by
      gcongr
    _ = Z^(5+ξ/2) := by
      rw [←Real.rpow_natCast (Z^(1:ℝ)) 2,←Real.rpow_mul hz.le,
        ←Real.rpow_sub hz,←Real.rpow_add hz]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

/-- The dyadic height and radius caps hold at every recovered first block
of a genuine packet, independently of the recovery fallback. -/
theorem recovered_main_dyadic_caps
    (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H)
    (Z A omega ξ : ℝ) (hZ : 1 < Z) (hA : 0 ≤ A) (homega : 0 ≤ omega)
    (hξ : ξ ≤ 1) (hsource₀ : 0 < sourceRadius src) (hsource : sourceRadius src ≤ Z^(1:ℝ))
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (n : (row x).FirstDyadic Kfirst (radius (row x).first (row x).E) (sourceRadius src)) :
    0 < secondScale fallback (mainScale src R seed Kfirst radius side Z A 1 omega)
      x.1.2.2.1 x.1.2.2.2 (row x) n ∧
    secondScale fallback (mainRadius src R seed Kfirst radius side Z A 1 omega ξ)
      x.1.2.2.1 x.1.2.2.2 (row x) n ≤ 1*Z^(6:ℝ) ∧
    0 < secondScale fallback (mainHeight src R seed Kfirst radius side)
      x.1.2.2.1 x.1.2.2.2 (row x) n ∧
    secondScale fallback (mainHeight src R seed Kfirst radius side)
      x.1.2.2.1 x.1.2.2.2 (row x) n ≤ Z^(1:ℝ) := by
  rw [secondScale_mainScale,secondScale_mainRadius,secondScale_mainHeight]
  let q := firstSourceOuterLabel src R seed Kfirst radius x.1.1
  have hc := first_actual_common_caps src R seed hs hz₁ hz₂ Kfirst radius x.1.1 Z hsource
  have hn : (1:ℝ) ≤ (q.sideCommon side).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (q.sideCommon_supported side).1)
  refine ⟨Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _,?_,?_,?_⟩
  · simpa only [mainRadius,one_mul] using
      firstLowRadius_polynomial_cap q side (sourceRadius src) Z A omega ξ hZ hA homega
        hξ hsource₀.le hsource hc.1 hc.2
  · exact div_pos hsource₀ (zero_lt_one.trans_le hn)
  · exact (div_le_self hsource₀.le hn).trans hsource


/-- Reference-sector transport for the recovered main scale; both
inequalities hold on every first dyadic representative of the packet. -/
theorem recovered_main_sector_bounds
    (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H)
    (ref : FirstJointLabel ι) (Z A M omega e : ℝ) (hZ : 1 < Z) (he : 0 ≤ e)
    (hc : |(firstSourceOuterLabel src R seed Kfirst radius x.1.1).sideWidth side Z-ref.sideWidth side Z| ≤ e)
    (hd : |(firstSourceOuterLabel src R seed Kfirst radius x.1.1).sideWidth (!side) Z-ref.sideWidth (!side) Z| ≤ e)
    (hR : |(firstSourceOuterLabel src R seed Kfirst radius x.1.1).activeWidth Z-ref.activeWidth Z| ≤ e)
    (hE : |(firstSourceOuterLabel src R seed Kfirst radius x.1.1).punctureWidth Z-ref.punctureWidth Z| ≤ e)
    (n : (row x).FirstDyadic Kfirst (radius (row x).first (row x).E) (sourceRadius src)) :
    secondScale fallback (mainScale src R seed Kfirst radius side Z A M omega)
        x.1.2.2.1 x.1.2.2.2 (row x) n ≤
      Z^(firstMainExponent A (ref.sideWidth side Z) (ref.sideWidth (!side) Z)
        (ref.activeWidth Z) (ref.punctureWidth Z) M (3/500) (omega+6*e)) ∧
    Z^(firstMainExponent A (ref.sideWidth side Z-e) (ref.sideWidth (!side) Z-e)
        (ref.activeWidth Z) (ref.punctureWidth Z) M (3/500) (omega-8*e)) ≤
      secondScale fallback (mainScale src R seed Kfirst radius side Z A M omega)
        x.1.2.2.1 x.1.2.2.2 (row x) n := by
  rw [secondScale_mainScale]
  exact firstLowMainScale_sector_bounds _ ref side Z A M omega e hZ he hc hd hR hE

end ActualFirstSecondSource
#print axioms firstLowMainScale_sector_bounds
#print axioms firstLowRadius_polynomial_cap
#print axioms ActualFirstSecondSource.recovered_main_dyadic_caps
#print axioms ActualFirstSecondSource.recovered_main_sector_bounds
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighDyadicGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighReferencePacketGates ; sha256 52eac846d23441e8a9dd81cd0d5bf5b46b3a5b87ddd0f7099798bc0631296c2d -/
section


/-! All scalar gates for the literal high packet are packaged at one
actual first reference. Source support and clipping fees are fixed, while
both sector meshes and the live amplifier frequency loss remain explicit. -/
set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization

 def highPacketGeometryLoss (e ξ : ℝ) := 10*e+2*lowLocalTiny+ξ/2+lowLocalTiny
 def highPacketLengthLoss (e : ℝ) := lowLocalTiny+2*lowLocalTiny+e
 def highPacketOmegaLoss (e₁ e₂ omega : ℝ) := omega+6*e₁+e₂
 def highPacketRowWidth (c d R L e ξ : ℝ) :=
   1-R-max (c-d) 0+L-6*(3/500)+highPacketGeometryLoss e ξ
 def highPacketMissingWidth (p R E R₀ e : ℝ) := p-R-E+R₀+4*e

structure HighReferencePacketGates
    (A c d p R R₀ E Bc L BR e₁ e₂ omega ξ b₂ g₂ t₂ : ℝ) : Prop where
  c_nonneg : 0 ≤ c
  c_cap : c ≤ 1
  d_nonneg : 0 ≤ d
  d_cap : d ≤ 1
  p_nonneg : 0 ≤ p
  p_le_c : p ≤ c
  p_le_d : p ≤ d
  R_nonneg : 0 ≤ R
  R_le_p : R ≤ p
  R₀_nonneg : 0 ≤ R₀
  R₀_le_R : R₀ ≤ R
  E_nonneg : 0 ≤ E
  Bc_nonneg : 0 ≤ Bc
  L_nonneg : 0 ≤ L
  cancellation : L ≤ 5*(R-R₀)
  A_cap : A ≤ 883/1000
  b_nonneg : 0 ≤ b₂
  g_le_b : g₂ ≤ b₂
  t_nonneg : 0 ≤ t₂
  geometry_nonneg : 0 ≤ highPacketGeometryLoss e₁ ξ
  length_nonneg : 0 ≤ highPacketLengthLoss e₁
  length_split : lowLocalTiny+2*lowLocalTiny+e₁ ≤ highPacketLengthLoss e₁
  row_cap : highPacketRowWidth c d R L e₁ ξ ≤ 6
  missing_cap : highPacketMissingWidth p R E R₀ e₁ ≤ 2
  conductor : highPacketRowWidth c d R L e₁ ξ+(BR+2)+lowLocalTiny ≤ highLocalDmax BR
  total_budget : highPacketOmegaLoss e₁ e₂ omega+lowLocalTiny+lowLocalTiny+lowLocalTiny+
    highPacketGeometryLoss e₁ ξ+highPacketLengthLoss e₁+4*e₁ ≤ 144011/109800000
  tail_cap : A-min c d+R+E-1+5*(3/500)+g₂-t₂-b₂+highPacketOmegaLoss e₁ e₂ omega ≤ 4
  target_lower : -2 ≤ p+A-c+R+E+Bc-144011/109800000
  row_budget : 1-R-max ((c-e₁)-(d-e₁)) 0+(L+e₁)-6*(3/500)-(omega-8*e₁)+
    2*lowLocalTiny+e₁+ξ/2+lowLocalTiny ≤ highPacketRowWidth c d R L e₁ ξ
  missing_budget : (p+e₁)-(R-e₁)-(E-e₁)+(R₀+e₁) ≤ highPacketMissingWidth p R E R₀ e₁
  scale_upper_loss : highPacketOmegaLoss e₁ e₂ omega-e₂ = omega+6*e₁
  prime_reserve : lowLocalTiny ≤ 144011/219600000
  final_saving : -(144011/219600000:ℝ)+lowLocalTiny+2*e₁ ≤ -1/10000

theorem actual_high_reference_packet_gates
    {ι : Type*} [Fintype ι] (ref : FirstJointLabel ι) (side : Bool)
    (Z A BR e₁ e₂ omega ξ b₂ g₂ t₂ : ℝ) (hZ : 1 < Z)
    (hC : (ref.C.absNorm : ℝ) ≤ Z^(1:ℝ)) (hD : (ref.D.absNorm : ℝ) ≤ Z^(1:ℝ))
    (hA₀ : 0 ≤ A) (hA : A ≤ 883/1000) (hBR : 0 ≤ BR)
    (he₁ : 0 ≤ e₁) (he₁cap : e₁ ≤ lowLocalTiny)
    (he₂ : 0 ≤ e₂) (he₂cap : e₂ ≤ lowLocalTiny)
    (homega : 0 ≤ omega) (homegaCap : omega ≤ lowLocalTiny)
    (hξ : 0 ≤ ξ) (hξCap : ξ ≤ lowLocalTiny)
    (hb₂ : 0 ≤ b₂) (hg₂ : g₂ ≤ b₂) (ht₂ : 0 ≤ t₂) :
    HighReferencePacketGates A (ref.sideWidth side Z) (ref.sideWidth (!side) Z)
      (ref.radicalWidth Z) (ref.activeWidth Z)
      (Real.logb Z ((canceledIdeal (ref.sideCommon side) (ref.sideCommon (!side)) 5).absNorm : ℝ))
      (ref.punctureWidth Z) (ref.sideAllowance side Z)
      (Real.logb Z (normValue (leftEffectiveFactor (ref.sideCommon side) (ref.sideCommon (!side)))))
      BR e₁ e₂ omega ξ b₂ g₂ t₂ := by
  rcases ref.high_reference_caps side Z hZ hC hD with
    ⟨hc,hc1,hd,hd1,hp,hp1,hR,hR1,hE,hE1,hBc⟩
  rcases ref.high_radical_reference Z hZ side with ⟨_,hpc,hpd,hRp⟩
  rcases ref.high_cancellation_reference side Z hZ with ⟨hL,hR₀,hR₀R,hcancel⟩
  have ht : 0 ≤ lowLocalTiny := by norm_num [lowLocalTiny]
  have hbudget := high_local_total_budget omega e₁ e₂ lowLocalTiny ξ lowLocalTiny lowLocalTiny
    (2*lowLocalTiny) homega homegaCap he₁ he₁cap he₂ he₂cap ht le_rfl hξ hξCap
    ht le_rfl ht le_rfl (by positivity) le_rfl
  have hgeomCap : highPacketGeometryLoss e₁ ξ ≤ 1/2 := by
    dsimp only [highPacketGeometryLoss]
    norm_num [lowLocalTiny] at he₁cap hξCap ⊢
    linarith
  have hmissingCap : 4*e₁ ≤ 1 := by norm_num [lowLocalTiny] at he₁cap ⊢;linarith
  have hwidths := high_local_row_missing_caps _ _ _ _ _ _ _ _ _ hc hd hp1 hR hRp hR₀ hE hL hcancel
    hgeomCap hmissingCap
  have homegaLoss : highPacketOmegaLoss e₁ e₂ omega ≤ 1 := by
    dsimp only [highPacketOmegaLoss]
    norm_num [lowLocalTiny] at homegaCap he₁cap he₂cap ⊢
    linarith
  have htail := high_local_tail_target_caps A _ _ _ _ _ _ b₂ g₂ t₂
    (highPacketOmegaLoss e₁ e₂ omega) hA₀ hA hc hc1 hd hp hR hR1 hE hE1 hBc hg₂ ht₂ homegaLoss
  refine ⟨hc,hc1,hd,hd1,hp,hpc,hpd,hR,hRp,hR₀,hR₀R,hE,hBc,hL,hcancel,hA,hb₂,hg₂,ht₂,
    hbudget.1,hbudget.2.1,le_rfl,hwidths.1,hwidths.2,
    high_local_conductor_budget BR _ hBR hwidths.1,hbudget.2.2.1,htail.1,htail.2,?_,?_,?_,
    hbudget.2.2.2.1,hbudget.2.2.2.2⟩
  · rw [first_row_sector_loss]
    dsimp only [highPacketRowWidth,highPacketGeometryLoss]
    linarith
  · rw [first_missing_sector_loss]
    exact le_rfl
  · dsimp only [highPacketOmegaLoss]
    ring

#print axioms actual_high_reference_packet_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighReferencePacketGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstNaturalFromAnnularExplicitMesh ; sha256 8e763ea75b4ca788b4a01832a3d8355a0c9e354563edda1eb62adadfcd1a818e -/
section





/-! The original natural energy follows from the actual annular source
targets. Plain and radial profiles are fixed before the final constant;
all geometric, support and normalization gates are proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalSource CenteredMomentLogDyadic
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentEnergyNaturalInputMatches CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance naturalFromAnnularExplicitSumDecEq : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

private theorem four_terms_height_explicit (a b c d X Y H : ℝ)
    (hX : 0 ≤ X) (hXY : X ≤ Y) (hH : 1 ≤ H) :
    a*X+b*Y+c*Y+d*H*Y ≤ (1+|a|+|b|+|c|+|d|)*H*Y := by
  have hY : 0 ≤ Y := hX.trans hXY
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have base (v : ℝ) : v*Y ≤ |v| *H*Y := by
    calc
      _ ≤ |v| *Y := mul_le_mul_of_nonneg_right (le_abs_self v) hY
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg v) hY]
  have ha : a*X ≤ |a| *H*Y := by
    calc
      _ ≤ |a| *X := mul_le_mul_of_nonneg_right (le_abs_self a) hX
      _ ≤ |a| *Y := mul_le_mul_of_nonneg_left hXY (abs_nonneg a)
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg a) hY]
  have hd : d*H*Y ≤ |d| *H*Y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self d) hH₀) hY
  nlinarith [base b,base c,mul_nonneg hH₀ hY]

variable (M : Ideal O) [NeZero M]
local instance naturalFromAnnularExplicitFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- For fixed plain and radial profiles, a uniform annular target gives
the original fourth-moment energy bound. The exact natural-state gates and
original coefficient family remain in the conclusion. -/
theorem actual_local_natural_from_annular_explicit_mesh
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Wslot : ℝ → ℂ) (aslot bslot lo hi a b bΦ Bmask ε ξ e : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hcSlot : ContDiff ℝ ∞ Wslot) (hbslot : 0 < bslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hε : 0 < ε) (hξ : 0 < ξ) (hξcap : ξ ≤ 1)
    (he : 0 < e) (heε : e ≤ ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ J : ℕ,
    ∀ (ηfirst η₀ : Character) (Q : Ideal O), Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∀ (p : Profiles a b) (Wradial : 𝓢(ℝ,ℂ)) (ν ηheight CAnn : ℝ),
      0 < ν → ν < ηheight → 0 ≤ CAnn →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ meshGuaranteed Bmask ε) →
    ∀ (hσlo : ∀ i,lo ≤ σ i) (hσhi : ∀ i,σ i ≤ hi),
      0 ≤ height → height ≤ Z^ν → (∀ i,|freq i| ≤ height) → |t| ≤ Z^ν →
    ∀ (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      410/1000 ≤ Real.logb Z X₁ → 410/1000 ≤ Real.logb Z X₂ →
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z X₁) (Real.logb Z X₂) (∑ i,w i) →
    ∀ s : NaturalState Z Bmask bΦ,
      s.fixedModulus = internalQ Q η₀ → s.character = ηfirst → s.rowWidth = 1 →
      s.characterWidth = Real.logb Z (ηfirst.modulus.absNorm : ℝ) → s.radial.profile = Wradial →
    let src := LocalFirstNaturalSource.input M H hH η₀ θ Wslot hcSlot.continuous
      aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩)
      s p ha t X₁ X₂ hX₁ hX₂;
    FirstNaturalAnnularTargets src s.puncture Z ξ t Wradial e ηheight CAnn →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        C*(1+|t|+height)^J*Z^(1+ε) := by
  obtain ⟨J,U,Sd,St,Cd,Ct,hCd,hCt,hnatural⟩ :=
    actual_local_first_natural_target_explicit_mesh (α := α) M H hH Wslot aslot bslot lo hi a b bΦ Bmask ε ξ
      haslot hsSlot hcSlot hbslot ha hlo hhi hbΦ hBmask hε hξ hbeta hbetaTop
  refine ⟨J,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72 p Wradial ν ηheight CAnn hν hgap hAnn
  obtain ⟨Cc,hCc,hnatural⟩ := hnatural ηfirst η₀ Q hQM hQzero hQtop hQ72
  let B₁ := SchwartzMap.seminorm ℝ 0 0 (p.profile 0)
  let B₂ := SchwartzMap.seminorm ℝ 0 0 (p.profile 1)
  have hB₁ : 0 ≤ B₁ := apply_nonneg _ _
  have hB₂ : 0 ≤ B₂ := apply_nonneg _ _
  let F := profileBound Wslot hcSlot.continuous aslot bslot lo hi haslot hsSlot
  let lower := aslot^Fintype.card α*a^2
  have hlower : 0 < lower := by dsimp only [lower];positivity
  obtain ⟨Ca,hCa,habsolute⟩ := eventually_original_first_absolute_from_annular_targets
    (ι := α) Wradial (Fintype.card α) ν ηheight F bslot b b B₁ B₂ a a lower e 0 (883/1000)
    hν hgap hB₁ hB₂ ha.le ha.le hlower he
  let K := firstSourceCoarseConstant (Fintype.card α) F bslot b b B₁ B₂
    (diagonalControl profile)
  let Pplain := F^Fintype.card α*B₁*B₂
  let ca := 2*Ca*(CAnn+K)
  let cd := 2*Cd*Pplain^2*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wradial
  let ct := 2*Ct*Pplain^2*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wradial
  let cc := 2*Cc*diagonalControl Wradial*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2
  refine ⟨1+|ca|+|cd|+|ct|+|cc|,by positivity,?_⟩
  filter_upwards [hnatural,habsolute,
    LocalFirstNaturalSource.eventually_join_geometry (α := α) M H hH Wslot hcSlot.continuous
      aslot bslot lo hi a b haslot hbslot hsSlot ha hhi] with Z hnatural habsolute hgeometry
  refine ⟨hnatural.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hheight hheightCap hfreq ht
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial src hannular
  have hZ := hnatural.1
  have hz := zero_lt_one.trans hZ
  have hwlocal : ∀ i,w i ≤ lowLocalMesh := fun i => (hwmesh i).trans (meshGuaranteed_le_lowLocalMesh Bmask ε)
  have hg := hgeometry.2 η₀ θ w σ freq (fun i => ⟨hσlo i,hσhi i⟩) Bmask bΦ s p
    t X₁ X₂ hX₁ hX₂ hw hwlocal hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity
  have hp := LocalFirstNaturalSource.plain_join_gates M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hlowerEq := LocalFirstNaturalSource.lower_profile_exact M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have haTarget := habsolute src s.puncture le_rfl (fun _ => le_rfl) le_rfl le_rfl le_rfl
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2
    (le_of_eq hlowerEq.symm) hg.source_positive (by simpa only [Real.rpow_one] using hg.source_cap)
    (Real.logb Z (volume src.toData)) hg.width_nonneg (hg.width_upper.trans (by norm_num)) hg.volume_eq
    ξ hξcap t CAnn ht hAnn
  have haBound := haTarget (by
    simpa only [FirstNaturalAnnularTargets,Real.rpow_logb hz hZ.ne' (volume_pos src.toData)] using hannular)
  have hpc := LocalFirstNaturalSource.plain_control M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hinitial := hnatural.2 θ w σ freq t height hw hwmesh hσlo hσhi hheight hfreq
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum s hQ hη hrow hwidth p
  change plainControl src (p.profile 0) (p.profile 1)=Pplain at hpc
  change energy _ _ _ _ _ _ _ _ _ _ _ _ _ _ ≤ _ at hinitial
  rw [hradial,hpc] at hinitial
  have hmain : (2/volume src.toData)*
      (∑ i : FirstSourceOuterIndex src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ),
        ‖firstPhysicalValue src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ)
          (fun _ => t) Wradial (fun _ => logAnnulus) i‖) ≤ ca*Z^(1+e) := by
    have hh := mul_le_mul_of_nonneg_left haBound (by norm_num : (0:ℝ) ≤ 2)
    convert hh using 1 <;> (try dsimp only [ca,K]) <;> ring
  have hH : 1 ≤ (1+|t|+height)^J := one_le_pow₀ (by linarith [abs_nonneg t])
  have hpow : Z^(1+e) ≤ Z^(1+ε) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hfour := four_terms_height_explicit ca cd ct cc (Z^(1+e)) (Z^(1+ε)) ((1+|t|+height)^J)
    (Real.rpow_nonneg hz.le _) hpow hH
  rw [hradial]
  apply hinitial.trans
  apply le_trans _ hfour
  dsimp only [cd,ct,cc]
  exact add_le_add (add_le_add (add_le_add hmain le_rfl) le_rfl) le_rfl

#print axioms actual_local_natural_from_annular_explicit_mesh
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstNaturalFromAnnularExplicitMesh -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighFirstNormGates ; sha256 f9f49615eaa0deac75d374cc17047c1017ce0e5064354e199f15b0f0eaac6e9f -/
section


/-! Every arithmetic first-row norm gate is inherited from the common
full eleven-coordinate first cell. The right side swaps only arithmetic
common ideals and the selected subset, preserving the original source. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstMixedRoot CenteredMomentSectorLocalization CanonicalRowCompletion
open CenteredMomentSupportedCorrelation CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstSourceConductorCaps
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma high_norm_bounds_of_log_close (Z n r e : ℝ) (hZ : 1 < Z) (hn : 0 < n)
    (h : |Real.logb Z n-r| < e) : Z^(r-e) ≤ n ∧ n ≤ Z^(r+e) := by
  have hh := abs_lt.mp h
  have hid := Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn
  constructor
  · rw [←hid]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · rw [←hid]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

namespace FirstJointLabel
lemma high_full_sector_norm_gates (q ref : FirstJointLabel ι) (side : Bool) (Z e : ℝ)
    (hZ : 1 < Z)
    (h : ∀ j, |q.fullWidthCoordinates Z j-ref.fullWidthCoordinates Z j| < e) :
    Z^(ref.sideWidth side Z-e) ≤ ((q.sideCommon side).absNorm : ℝ) ∧
    normValue q.puncture ≤ Z^(ref.punctureWidth Z+e) ∧
    normValue (leftEffectiveFactor (q.sideCommon side) (q.sideCommon (!side))) ≤
      Z^(Real.logb Z (normValue (leftEffectiveFactor (ref.sideCommon side) (ref.sideCommon (!side))))+e) ∧
    Z^(ref.activeWidth Z-e) ≤ normValue (activeConductor q.C q.D) ∧
    Z^(ref.punctureWidth Z-e) ≤ normValue q.puncture ∧
    ((commonRadical q.C q.D).absNorm : ℝ) ≤ Z^(ref.radicalWidth Z+e) ∧
    ((canceledIdeal (q.sideCommon side) (q.sideCommon (!side)) 5).absNorm : ℝ) ≤
      Z^(Real.logb Z ((canceledIdeal (ref.sideCommon side) (ref.sideCommon (!side)) 5).absNorm : ℝ)+e) := by
  have hh := q.first_widths_close_of_full ref Z e h
  have hc : |q.sideWidth side Z-ref.sideWidth side Z| < e := by
    cases side
    · exact hh 1
    · exact hh 0
  have hE : |Real.logb Z (normValue q.puncture)-ref.punctureWidth Z| < e := by
    have hhE : |q.punctureWidth Z-ref.punctureWidth Z| < e := hh 4
    simpa only [punctureWidth,normValue,eisEmbedding_norm_sq_eq_absNorm_span] using hhE
  have hA : |Real.logb Z (normValue (activeConductor q.C q.D))-ref.activeWidth Z| < e := hh 3
  have hp : |Real.logb Z ((commonRadical q.C q.D).absNorm : ℝ)-ref.radicalWidth Z| < e := hh 2
  have hcancel := q.cancellation_widths_close_of_full ref side Z e h
  have hcB := high_norm_bounds_of_log_close Z _ _ e hZ
    (CenteredMomentFirstScale.norm_pos _ (q.sideCommon_supported side).1) hc
  have heB := high_norm_bounds_of_log_close Z _ _ e hZ
    (normValue_pos _ (supported_element_ne_zero _ (subsetGenerator_supported q.C q.D q.hC q.E))) hE
  have haB := high_norm_bounds_of_log_close Z _ _ e hZ
    (normValue_pos _ (supported_element_ne_zero _ (activeConductor_supported q.C q.D q.hC))) hA
  have hpB := high_norm_bounds_of_log_close Z _ _ e hZ
    (CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero q.C q.D)) hp
  have hfB := high_norm_bounds_of_log_close Z _ _ e hZ
    (normValue_pos _ (show leftEffectiveFactor (q.sideCommon side) (q.sideCommon (!side)) ≠ 0 from
      active_product_pow_ne_zero _ _ (q.sideCommon_supported side) _)) hcancel.1
  have hrB := high_norm_bounds_of_log_close Z _ _ e hZ
    (CenteredMomentFirstScale.norm_pos _ (canceledIdeal_ne_zero _ _ (q.sideCommon_supported side) 5)) hcancel.2
  exact ⟨hcB.1,heB.2,hfB.2,haB.1,heB.1,hpB.2,hrB.2⟩
end FirstJointLabel

namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

/-- The exact seven norm gates consumed by high source row geometry. -/
theorem packet_first_norm_gates
    (x : Packet src R seed Kfirst radius side K Radius H)
    (ref : FirstJointLabel ι) (Z e : ℝ) (hZ : 1 < Z)
    (h : ∀ j, |(firstSourceOuterLabel src R seed Kfirst radius x.1.1).fullWidthCoordinates Z j-
      ref.fullWidthCoordinates Z j| < e) :
    Z^(ref.sideWidth side Z-e) ≤ ((row x).label.C₁.absNorm : ℝ) ∧
    normValue (primeSubsetGenerator (fun P : CommonIndex (row x).label.C₁ (row x).label.D₁ => P.val)
      (row x).label.E) ≤ Z^(ref.punctureWidth Z+e) ∧
    normValue (leftEffectiveFactor (row x).label.C₁ (row x).label.D₁) ≤
      Z^(Real.logb Z (normValue (leftEffectiveFactor (ref.sideCommon side) (ref.sideCommon (!side))))+e) ∧
    Z^(ref.activeWidth Z-e) ≤ normValue (activeConductor (row x).label.C₁ (row x).label.D₁) ∧
    Z^(ref.punctureWidth Z-e) ≤ normValue (primeSubsetGenerator
      (fun P : CommonIndex (row x).label.C₁ (row x).label.D₁ => P.val) (row x).label.E) ∧
    ((commonRadical (row x).label.C₁ (row x).label.D₁).absNorm : ℝ) ≤ Z^(ref.radicalWidth Z+e) ∧
    ((canceledIdeal (row x).label.C₁ (row x).label.D₁ 5).absNorm : ℝ) ≤
      Z^(Real.logb Z ((canceledIdeal (ref.sideCommon side) (ref.sideCommon (!side)) 5).absNorm : ℝ)+e) := by
  let q := firstSourceOuterLabel src R seed Kfirst radius x.1.1
  have hh := q.high_full_sector_norm_gates ref side Z e hZ h
  have hC : (row x).label.C₁=q.sideCommon side := by cases side <;> rfl
  have hD : (row x).label.D₁=q.sideCommon (!side) := by cases side <;> rfl
  have hEp : primeSubsetGenerator (fun P : CommonIndex (row x).label.C₁ (row x).label.D₁ => P.val)
      (row x).label.E=q.puncture := by
    cases side
    · exact swappedFirstSubset_generator _ _ _
    · rfl
  have hAct : normValue (activeConductor (row x).label.C₁ (row x).label.D₁)=
      normValue (activeConductor q.C q.D) := by
    cases side
    · change normValue (activeConductor q.D q.C)=normValue (activeConductor q.C q.D)
      simp only [normValue,active_span_swap]
    · rfl
  have hrad : commonRadical (row x).label.C₁ (row x).label.D₁=commonRadical q.C q.D := by
    cases side
    · change commonRadical q.D q.C=commonRadical q.C q.D
      unfold commonRadical
      rw [Finset.inter_comm]
    · rfl
  rw [hEp,hAct,hrad,hC,hD]
  exact hh

end ActualFirstSecondSource
#print axioms FirstJointLabel.high_full_sector_norm_gates
#print axioms ActualFirstSecondSource.packet_first_norm_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighFirstNormGates -/
