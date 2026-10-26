/- Copyright (c) 2026 Sil. Apache-2.0.
The literal root Source for the collision/inverse restoration family.
This file constructs data and proves exact identities and numerical gates.
It contains no moment or source-energy hypothesis or conclusion.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RestoredRootDictionary
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstCanonicalGeometry
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstPuncturedReference
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstChosenEnergy
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RestoredRootSource
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentLattice
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.Record1252270103Source
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentUncenteredTerminal
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRectangle
open CenteredMomentEnergyBands CenteredMomentAddedZeroUniform
open CenteredMomentAllocatedNaturalRadial
open CenteredMomentTwist
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowProfiles
open KernelRowPools KernelPunctureRows KernelLabelledSlots
open NativeFiniteHoles NativeInjectiveEnergy ReferencePrimeEnclosure
open MixedCommonCoefficient MixedCanonicalSource MixedFrozenSource MixedPrincipalPair
open MixedPrincipalHeights MixedPrincipalWindow MixedPrincipalAllocations MixedFirstSeededSource
open MixedFirstPuncturedReference MixedFirstActualNonexceptional
open MixedFirstGeometricCaps MixedFirstChosenEnergy RestoredRootDictionary
open MixedFirstRebase
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type*} [Fintype ι]

theorem comparison_value : comparisonScale (9/4:ℝ) = 2/9 := by
  norm_num [comparisonScale]

/-- The one marked-profile bound is chosen before every root, height,
ray label and ordinary Schwartz profile. -/
def slotBound (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) : ℝ :=
  Classical.choose (slot_profile_bound W hW hWs (33/50) (33/50))

theorem slotBound_spec (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) :
    1 ≤ slotBound W hW hWs ∧ ∀ f x : ℝ,
      ‖slotProfile W (33/50) f x‖ ≤ slotBound W hW hWs := by
  have h := Classical.choose_spec (slot_profile_bound W hW hWs (33/50) (33/50))
  exact ⟨h.1,fun f x => h.2 _ f le_rfl le_rfl x⟩

variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M ≤ Hray)

/-- Actual canonical input data. The lower length conditions select the
complement of the exact zero branch; they do not require lengths >= 1.
The numerical upper bounds are supplied by `face_root_gates` below. -/
structure Data (ι : Type*) [Fintype ι] where
  Z : ℝ
  hZ : 1 < Z
  Lcap : ℝ
  hLcap : 8 ≤ Lcap
  W : ℝ → ℂ
  hW : Continuous W
  hWs : Function.support W ⊆ Icc (1:ℝ) 2
  η₀ : Character
  θ : ι → RayQuotient.Characters M Hray
  w : ι → ℝ
  freq : ι → ℝ
  hw : ∀ i, 0 ≤ w i
  hwcap : ∀ i, w i ≤ 3/50
  R₀ : ι → Finset Id
  t : ℝ
  p : Profiles (1/4) (9/4)
  X₁ : ℝ
  X₂ : ℝ
  hx₁ : comparisonScale (9/4) < X₁
  hx₂ : comparisonScale (9/4) < X₂
  hcap₁ : X₁ ≤ Z
  hcap₂ : X₂ ≤ Z

namespace Data
variable {M Hray}
variable (r : Data M Hray ι)

def pool (i : ι) : Finset Id :=
  supportedPool (CenteredMomentPrimeSlot.primePool M Hray 2 (r.Z^(r.w i)))

def characters (i : ι) : Character := relativeCharacter M Hray hHray r.η₀ (r.θ i)

theorem pool_prime (i : ι) (I : Id) (hI : I ∈ r.pool i) : Prime I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.1

theorem pool_norm (i : ι) (I : Id) (hI : I ∈ r.pool i) :
    Supported I ∧ (I.absNorm:ℝ) ≤ 2*r.Z^(r.w i) := by
  have hi := Finset.mem_filter.mp hI
  exact ⟨hi.2,canonical_pool_norm_le M Hray _
    (Real.rpow_pos_of_pos (zero_lt_one.trans r.hZ) _) I hi.1⟩

theorem pool_enclosed (i : ι) : r.pool i ⊆ primeValues (enclosure (16*r.Z^r.Lcap)) := by
  rw [enclosure_values]
  exact canonical_pool_enclosed M Hray r.Z (r.w i) r.Lcap 16 r.hZ.le
    ((r.hwcap i).trans (by linarith [r.hLcap])) (by norm_num)

theorem ordinary_caps :
    (9/4:ℝ)*max r.X₁ (comparisonScale (9/4)) ≤ 16*r.Z^r.Lcap ∧
    (9/4:ℝ)*max r.X₂ (r.X₁*r.X₂/comparisonScale (9/4)) ≤ 16*r.Z^r.Lcap := by
  have hz : 0 < r.Z := zero_lt_one.trans r.hZ
  have hx₁ : 0 < r.X₁ := (comparisonScale_pos _).trans r.hx₁
  have hx₂ : 0 < r.X₂ := (comparisonScale_pos _).trans r.hx₂
  have hZ₁ : r.Z ≤ r.Z^r.Lcap := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le r.hZ.le (show (1:ℝ) ≤ r.Lcap by linarith [r.hLcap]))
  have hZ₂ : r.Z*r.Z ≤ r.Z^r.Lcap := by
    calc
      r.Z*r.Z = r.Z^(2:ℝ) := by rw [Real.rpow_two]; ring
      _ ≤ r.Z^r.Lcap := Real.rpow_le_rpow_of_exponent_le r.hZ.le (by linarith [r.hLcap])
  have hprod : r.X₁*r.X₂ ≤ r.Z*r.Z :=
    mul_le_mul r.hcap₁ r.hcap₂ hx₂.le hz.le
  have h₁ : (9/4:ℝ)*r.X₁ ≤ 16*r.Z^r.Lcap := by
    nlinarith [r.hcap₁.trans hZ₁,Real.rpow_nonneg hz.le r.Lcap]
  have h₂ : (9/4:ℝ)*r.X₂ ≤ 16*r.Z^r.Lcap := by
    nlinarith [r.hcap₂.trans hZ₁,Real.rpow_nonneg hz.le r.Lcap]
  have hc : (9/4:ℝ)*(r.X₁*r.X₂/comparisonScale (9/4)) ≤ 16*r.Z^r.Lcap := by
    rw [comparison_value]
    nlinarith [hprod.trans hZ₂,Real.rpow_nonneg hz.le r.Lcap]
  constructor
  · simpa only [max_eq_left r.hx₁.le] using h₁
  · rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 9/4)]
    exact max_le h₂ hc

/-- All ordinary punctures are trivial; the collision/inverse holes
occur only in the literal canonical marked coefficient `R₀`. -/
def source : Source ι (1/4) (9/4) where
  S := enclosure (16*r.Z^r.Lcap)
  H := ∅
  pool := r.pool
  d := (1,1)
  hd := ⟨one_ne_zero,one_ne_zero⟩
  B := fun _ => 1
  hB := fun _ => one_ne_zero
  G := 1
  R := 1
  Fhole := 1
  hprod := by simp [finiteTupleProduct]
  hR := one_ne_zero
  hFhole := one_ne_zero
  ν := slotCoefficient (r.characters hHray) r.R₀ r.t
  Wslot := fun i => slotProfile r.W (33/50) (r.freq i)
  P := fun i => r.Z^(r.w i)
  M := fun _ => slotBound r.W r.hW r.hWs
  W₁ := r.p.profile 0
  W₂ := r.p.profile 1
  hs₁ := r.p.support 0
  hs₂ := r.p.support 1
  t₁ := r.t
  t₂ := r.t
  X₁ := r.X₁
  X₂ := r.X₂
  Y₁ := comparisonScale (9/4)
  Y₂ := r.X₁*r.X₂/comparisonScale (9/4)
  U₁ := max r.X₁ (comparisonScale (9/4))
  U₂ := max r.X₂ (r.X₁*r.X₂/comparisonScale (9/4))
  T := r.X₁*r.X₂
  L := comparisonScale (9/4)
  hL := comparisonScale_pos _
  hX₁ := r.hx₁.le
  hX₂ := r.hx₂.le
  hY₁ := le_rfl
  hY₂ := (le_div_iff₀ (comparisonScale_pos _)).mpr
    (mul_le_mul r.hx₁.le r.hx₂.le (comparisonScale_pos _).le
      ((comparisonScale_pos _).trans r.hx₁).le)
  hXU₁ := le_max_left _ _
  hXU₂ := le_max_left _ _
  hYU₁ := le_max_right _ _
  hYU₂ := le_max_right _ _
  hpX := rfl
  hpY := by field_simp [(comparisonScale_pos (9/4:ℝ)).ne']
  hP := fun i => Real.one_le_rpow r.hZ.le (r.hw i)
  hM := fun _ => (slotBound_spec r.W r.hW r.hWs).1
  hpool := r.pool_enclosed
  hp := r.pool_prime
  hpn := r.pool_norm
  hν := slot_coefficient_norm _ _ _
  hWnorm := fun i x => (slotBound_spec r.W r.hW r.hWs).2 (r.freq i) x
  hW := fun i => (slot_profile_support _ _ _).trans r.hWs
  hS := fun P hP => (enclosure_bound _ P hP).1
  hH := by simp
  henclose := by
    intro I hI hlen
    simp only [one_mul,map_one,Nat.cast_one,div_one] at hlen
    exact support_enclosed _ I hI
      (hlen.elim (fun h => h.trans r.ordinary_caps.1) (fun h => h.trans r.ordinary_caps.2))

theorem source_canonical : Canonical M Hray hHray r.W 16 r.Lcap r.Z r.η₀ r.θ r.w
    (fun _ => 33/50) r.freq r.t r.R₀ (r.source hHray) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem source_original_enclosure : OriginalEnclosure (r.source hHray) := by
  intro I hI hlen
  simpa only [source,one_mul,map_one,Nat.cast_one,div_one] using
    (r.source hHray).henclose I hI (by simpa only [source,one_mul,map_one,Nat.cast_one,div_one] using hlen)

theorem source_trivial_masks :
    (r.source hHray).H = ∅ ∧ (r.source hHray).R = 1 ∧
    (r.source hHray).Fhole = 1 ∧ (r.source hHray).d = (1,1) ∧
    (r.source hHray).G = 1 ∧ (r.source hHray).B = (fun _ => 1) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The actual original enclosure already contains the marked pool. -/
theorem pool_original_enclosed (i : ι) :
    r.pool i ⊆ primeValues (enclosure (4*r.Z^(2:ℝ))) := by
  rw [enclosure_values]
  exact canonical_pool_enclosed M Hray r.Z (r.w i) 2 4 r.hZ.le
    ((r.hwcap i).trans (by norm_num)) (by norm_num)

theorem original_ordinary_caps :
    (9/4:ℝ)*r.X₁ ≤ 4*r.Z^(2:ℝ) ∧ (9/4:ℝ)*r.X₂ ≤ 4*r.Z^(2:ℝ) := by
  have hz : 0 ≤ r.Z^(2:ℝ) := Real.rpow_nonneg (zero_lt_one.trans r.hZ).le _
  have hpow : r.Z ≤ r.Z^(2:ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le r.hZ.le (by norm_num : (1:ℝ) ≤ 2))
  have hmul (X : ℝ) (hX : X ≤ r.Z^(2:ℝ)) : (9/4:ℝ)*X ≤ 4*r.Z^(2:ℝ) :=
    (mul_le_mul_of_nonneg_left hX (by norm_num : (0:ℝ) ≤ 9/4)).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (9/4:ℝ) ≤ 4) hz)
  exact ⟨hmul r.X₁ (r.hcap₁.trans hpow),hmul r.X₂ (r.hcap₂.trans hpow)⟩

/-- Lorig=3 covers all four ordinary lengths. Lcap is chosen later above
both 8 and the actual N*mesh cap. The reference is NOT forced above one. -/
theorem source_length_caps (hZ5 : 5 ≤ r.Z) :
    (r.source hHray).X₁ ≤ r.Z^(3:ℝ) ∧ (r.source hHray).X₂ ≤ r.Z^(3:ℝ) ∧
    (r.source hHray).Y₁ ≤ r.Z^(3:ℝ) ∧ (r.source hHray).Y₂ ≤ r.Z^(3:ℝ) := by
  have hz : 0 < r.Z := zero_lt_one.trans r.hZ
  have hpow : r.Z ≤ r.Z^(3:ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le r.hZ.le (by norm_num : (1:ℝ) ≤ 3))
  have hx₁ := (comparisonScale_pos _).trans r.hx₁
  have hx₂ := (comparisonScale_pos _).trans r.hx₂
  have hprod : r.X₁*r.X₂ ≤ r.Z*r.Z := mul_le_mul r.hcap₁ r.hcap₂ hx₂.le hz.le
  refine ⟨r.hcap₁.trans hpow,r.hcap₂.trans hpow,r.hx₁.le.trans (r.hcap₁.trans hpow),?_⟩
  change r.X₁*r.X₂/comparisonScale (9/4) ≤ r.Z^(3:ℝ)
  rw [comparison_value]
  have hp : r.Z^(3:ℝ) = r.Z*r.Z*r.Z := by norm_num [Real.rpow_natCast,pow_succ,pow_two]
  rw [hp]
  have hscale := mul_le_mul_of_nonneg_right
    (show (9/2:ℝ) ≤ r.Z by linarith) (mul_self_nonneg r.Z)
  nlinarith

end Data

theorem enclosure_mono {C C' : ℝ} (h : C ≤ C') : enclosure C ⊆ enclosure C' := by
  intro P hP
  have hb := enclosure_bound C P hP
  have hp : P.val ∈ ReferencePrimeEnclosure.primePool C' :=
    Finset.mem_filter.mpr ⟨(mem_idealBall _ _).mpr ⟨P.property.ne_zero,hb.2.trans h⟩,
      P.property,hb.1⟩
  exact Finset.mem_image.mpr ⟨⟨P.val,hp⟩,Finset.mem_attach _ _,Subtype.ext rfl⟩

theorem original_enclosure_subset (Z Lcap : ℝ) (hZ : 1 < Z) (hLcap : 8 ≤ Lcap) :
    enclosure (4*Z^(2:ℝ)) ⊆ enclosure (16*Z^Lcap) := by
  apply enclosure_mono
  exact mul_le_mul (by norm_num : (4:ℝ) ≤ 16)
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by norm_num)

set_option maxHeartbeats 800000 in
/-- Trivial ordinary punctures really disappear from the exact tuple
dictionary; the marked `R₀` coefficients are not changed. -/
theorem rectangle_unpunctured (χ : Character) (S : Finset PrimeIdeal)
    (pool : ι → Finset Id) (hpool : ∀ i,pool i ⊆ primeValues S)
    (hp : ∀ i I,I ∈ pool i → Prime I)
    (ν : ι → Character) (R₀ : ι → Finset Id) (t : ℝ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (hW₀ : W₁ 0 = 0) (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Iic b) (hs₂ : Function.support W₂ ⊆ Iic b)
    (hoff : ∀ I,¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I,Supported I →
      ((I.absNorm:ℝ) ≤ b*X₁ ∨ (I.absNorm:ℝ) ≤ b*X₂) → primeSupport I ⊆ primeValues S) :
    rectangleRow χ S ∅ 1 pool (slotCoefficient ν R₀ t) Wslot P W₁ W₂ b X₁ X₂ =
      RestorationFamily.row false S χ pool
        (fun i I => slotCoefficient ν R₀ t i I*Wslot i (I.absNorm/P i)) P W₁ W₂ b X₁ X₂ := by
  have hholes : enlargedHoles S ∅ (1:Id) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    have hd := (Finset.mem_filter.mp hQ).2
    exact Q.property.not_isUnit (isUnit_of_dvd_one (hd.resolve_left (by simp)))
  have hsupport : primeSupport (1:Id) = ∅ := by
    exact congrArg Multiset.toFinset UniqueFactorizationMonoid.normalizedFactors_one
  have haug (live : S → Bool) : KernelPunctureRows.augmented S ∅ live = live := by
    funext P
    simp only [KernelPunctureRows.augmented,Finset.notMem_empty,decide_false,Bool.or_false]
  have he := rectangle_row_eq χ S ∅ 1 one_ne_zero pool hpool hp ν R₀ t
    Wslot P W₁ W₂ hW₀ b X₁ X₂ hX₁ hX₂ hs₁ hs₂ hoff henclose
  simpa only [hholes,hsupport,Finset.union_empty,MixedCenteredEnergy.puncturedRow,
    RestorationFamily.row,sourceValue,Bool.false_eq_true,ite_false,
    haug] using he

/-- The original (unraised) ordinary profiles are stored in Source and
both physical norm-power frequencies are t. This prevents a double twist.
The equality includes the original natural product normalization. -/
theorem source_row (r : Data M Hray ι) (χ : Character)
    (hoff : ∀ I,¬Supported I → idealCoeff χ I = 0) :
    weightedRow (r.source hHray) (by norm_num) 1 (idealCoeff χ) =
      RestorationFamily.row false (r.source hHray).S χ r.pool
        (fun i I => slotCoefficient (r.characters hHray) r.R₀ r.t i I *
          slotProfile r.W (33/50) (r.freq i) (I.absNorm/r.Z^(r.w i)))
        (fun i => r.Z^(r.w i))
        (normPowerProfile (r.p.profile 0) (1/4) (9/4) (by norm_num)
          (r.p.support 0) ((r.p.profile 0).smooth ⊤) r.t)
        (normPowerProfile (r.p.profile 1) (1/4) (9/4) (by norm_num)
          (r.p.support 1) ((r.p.profile 1).smooth ⊤) r.t) (9/4) r.X₁ r.X₂ := by
  rw [weighted_row_uncentered (r.source hHray) (by norm_num) rfl rfl χ]
  apply rectangle_unpunctured χ _ r.pool r.pool_enclosed r.pool_prime
  · by_contra h
    have hh := r.p.support 0 (normPowerProfile_support _ _ _ _ _ _ _ h)
    norm_num at hh
  · exact (comparisonScale_pos _).trans r.hx₁
  · exact (comparisonScale_pos _).trans r.hx₂
  · exact fun x hx => (r.p.support 0 (normPowerProfile_support _ _ _ _ _ _ _ hx)).2
  · exact fun x hx => (r.p.support 1 (normPowerProfile_support _ _ _ _ _ _ _ hx)).2
  · exact hoff
  · intro I hI hi
    exact support_enclosed _ I hI (hi.elim
      (fun h => h.trans ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans r.ordinary_caps.1))
      (fun h => h.trans ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans r.ordinary_caps.2)))

/-- Complete zero extension from the literal 4Z² restoration enclosure
to the canonical Source enclosure. No new marked values or ordinary
restrictions survive: every added term is proved zero by the dictionary. -/
theorem original_row_source (r : Data M Hray ι) (χ : Character)
    (hoff : ∀ I,¬Supported I → idealCoeff χ I = 0) :
    RestorationFamily.row false (enclosure (4*r.Z^(2:ℝ))) χ r.pool
        (fun i I => slotCoefficient (r.characters hHray) r.R₀ r.t i I *
          slotProfile r.W (33/50) (r.freq i) (I.absNorm/r.Z^(r.w i)))
        (fun i => r.Z^(r.w i))
        (normPowerProfile (r.p.profile 0) (1/4) (9/4) (by norm_num)
          (r.p.support 0) ((r.p.profile 0).smooth ⊤) r.t)
        (normPowerProfile (r.p.profile 1) (1/4) (9/4) (by norm_num)
          (r.p.support 1) ((r.p.profile 1).smooth ⊤) r.t) (9/4) r.X₁ r.X₂ =
      weightedRow (r.source hHray) (by norm_num) 1 (idealCoeff χ) := by
  rw [source_row M Hray hHray r χ hoff]
  apply row_enclosure false _ _ (original_enclosure_subset r.Z r.Lcap r.hZ r.hLcap) χ r.pool
    _ _ r.pool_original_enclosed
  · exact (comparisonScale_pos _).trans r.hx₁
  · exact (comparisonScale_pos _).trans r.hx₂
  · exact fun x hx => (r.p.support 0 (normPowerProfile_support _ _ _ _ _ _ _ hx)).2
  · exact fun x hx => (r.p.support 1 (normPowerProfile_support _ _ _ _ _ _ _ hx)).2
  · exact hoff
  · intro I hI hi
    exact support_enclosed _ I hI (hi.elim
      (fun h => h.trans r.original_ordinary_caps.1) (fun h => h.trans r.original_ordinary_caps.2))

/-- The only character-zero input in the preceding exact identity is
automatically supplied on the ORIGINAL initial retained rows. -/
theorem natural_original_row_source (r : Data M Hray ι) (η : Character)
    (Q : Id) (z : O) (hz : CenteredMomentDetectorEnergyInitialState.initialKeep η Q z) :
    RestorationFamily.row false (enclosure (4*r.Z^(2:ℝ))) (naturalCharacter η z) r.pool
        (fun i I => slotCoefficient (r.characters hHray) r.R₀ r.t i I *
          slotProfile r.W (33/50) (r.freq i) (I.absNorm/r.Z^(r.w i)))
        (fun i => r.Z^(r.w i))
        (normPowerProfile (r.p.profile 0) (1/4) (9/4) (by norm_num)
          (r.p.support 0) ((r.p.profile 0).smooth ⊤) r.t)
        (normPowerProfile (r.p.profile 1) (1/4) (9/4) (by norm_num)
          (r.p.support 1) ((r.p.profile 1).smooth ⊤) r.t) (9/4) r.X₁ r.X₂ =
      weightedRow (r.source hHray) (by norm_num) 1 (idealCoeff (naturalCharacter η z)) :=
  original_row_source M Hray hHray r (naturalCharacter η z)
    (natural_character_off_supported η z ((initial_keep_iff η Q z).mp hz).1)

/-- Small positive ordinary lengths are an exact zero case, including
the equality boundary c. No lower power bound on an arbitrary Y is used. -/
theorem small_row (S : Finset PrimeIdeal) (χ : Character)
    (pool : ι → Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hsmall : X₁ ≤ comparisonScale (9/4) ∨ X₂ ≤ comparisonScale (9/4)) :
    RestorationFamily.row false S χ pool β P W₁ W₂ (9/4) X₁ X₂ = 0 :=
  literal_row_comparison_small false S χ pool β P W₁ W₂ (9/4) X₁ X₂ (by norm_num) hsmall

/-- Actual input width has at least unit width whenever its physical
radius covers Z. The fixed presentation and conductor factors are kept. -/
theorem input_width_one (η : Character) (K Z : ℝ) (hZ : 1 < Z) (hK : Z ≤ K) :
    1 ≤ inputWidth η K Z := by
  have hk : 1 ≤ Real.logb Z K := by
    simpa only [Real.logb_self_eq_one hZ] using
      (Real.logb_le_logb_of_le hZ (zero_lt_one.trans hZ) hK)
  have hη := Real.logb_nonneg hZ (ideal_norm_one_le η.modulus_ne_bot)
  have hp := Real.logb_nonneg hZ fixed_presentation_one_le
  unfold inputWidth
  linarith

/-- Exact global-face admission, inherited by all shortened ordinary
lengths and by every surviving singleton slot set. This is a numerical
root gate, not an application of the still-pending source theorem. -/
theorem face_root_gates {α : Type*} [Fintype α]
    (Z X₁ X₂ Y₁ Y₂ : ℝ) (w : α → ℝ) (hw : ∀ i,0 ≤ w i)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hy₁ : Y₁ ≤ X₁) (hy₂ : Y₂ ≤ X₂)
    (hface : (globalFace (99999/100000) (93/25) (3/50)).Admissible
      (length Z X₁) (length Z X₂) (∑ i,w i) 1)
    (T : Finset α) (η : Character) (K : ℝ) (hK : Z ≤ K) :
    Y₁ ≤ Z ∧ Y₂ ≤ Z ∧
    (∀ i : T,0 ≤ w i.val ∧ w i.val ≤ 3/50) ∧
    (∑ i : T,w i.val) ≤ 3/50 ∧
    Real.logb Z (Y₁*Y₂)+(93/25)*(∑ i : T,w i.val) ≤
      inputWidth η K Z-1/100000 := by
  have hs : 0 ≤ ∑ i,w i := Finset.sum_nonneg (fun i _ => hw i)
  obtain ⟨hcap,hbudget⟩ := (globalFace_admissible_iff
    (length_nonneg Z X₁ hZ) (length_nonneg Z X₂ hZ) hs (by norm_num : (0:ℝ) ≤ 93/25)).mp hface
  simp only [mul_one] at hcap hbudget
  have hsub : (∑ i : T,w i.val) ≤ ∑ i,w i := by
    rw [Finset.sum_coe_sort T (fun i => w i)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hw i)
  have hlog₁ : Real.logb Z Y₁ ≤ length Z X₁ :=
    Real.logb_le_logb_of_le hZ hY₁ (hy₁.trans (le_max_right _ _))
  have hlog₂ : Real.logb Z Y₂ ≤ length Z X₂ :=
    Real.logb_le_logb_of_le hZ hY₂ (hy₂.trans (le_max_right _ _))
  have hlen₁ : length Z X₁ ≤ 1 := by
    nlinarith [length_nonneg Z X₂ hZ]
  have hlen₂ : length Z X₂ ≤ 1 := by
    nlinarith [length_nonneg Z X₁ hZ]
  have hYcap (Y : ℝ) (hY : 0 < Y) (hlog : Real.logb Z Y ≤ 1) : Y ≤ Z := by
    calc
      Y = Z^(Real.logb Z Y) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hY).symm
      _ ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le hlog
      _ = Z := Real.rpow_one _
  refine ⟨hYcap Y₁ hY₁ (hlog₁.trans hlen₁),hYcap Y₂ hY₂ (hlog₂.trans hlen₂),?_,hsub.trans hcap,?_⟩
  · intro i
    have hi : w i.val ≤ ∑ j,w j := Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ _)
    exact ⟨hw _,hi.trans hcap⟩
  · rw [Real.logb_mul hY₁.ne' hY₂.ne']
    have hr := input_width_one η K Z hZ hK
    nlinarith

/-- A direct constructor on the actual surviving subset of the original
slots. Use T=remainingSet r A and R₀=the literal restorationHoles; no
estimate or compatibility premise is requested by this constructor. -/
def fromFace {α : Type*} [Fintype α]
    (Z Lcap : ℝ) (hZ : 1 < Z) (hLcap : 8 ≤ Lcap)
    (W : ℝ → ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (η₀ : Character) (θ : α → RayQuotient.Characters M Hray)
    (w freq : α → ℝ) (hw : ∀ i,0 ≤ w i) (t : ℝ)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ Y₁ Y₂ : ℝ)
    (hy₁ : Y₁ ≤ X₁) (hy₂ : Y₂ ≤ X₂)
    (hn₁ : comparisonScale (9/4) < Y₁) (hn₂ : comparisonScale (9/4) < Y₂)
    (hface : (globalFace (99999/100000) (93/25) (3/50)).Admissible
      (length Z X₁) (length Z X₂) (∑ i,w i) 1)
    (T : Finset α) (R₀ : T → Finset Id) : Data M Hray T := by
  have hg := face_root_gates Z X₁ X₂ Y₁ Y₂ w hw hZ
    ((comparisonScale_pos _).trans hn₁) ((comparisonScale_pos _).trans hn₂)
    hy₁ hy₂ hface T η₀ Z le_rfl
  exact {
    Z := Z, hZ := hZ, Lcap := Lcap, hLcap := hLcap
    W := W, hW := hW, hWs := hWs
    η₀ := η₀, θ := fun i => θ i.val
    w := fun i => w i.val, freq := fun i => freq i.val
    hw := fun i => (hg.2.2.1 i).1
    hwcap := fun i => (hg.2.2.1 i).2
    R₀ := R₀, t := t, p := p
    X₁ := Y₁, X₂ := Y₂, hx₁ := hn₁, hx₂ := hn₂
    hcap₁ := hg.1, hcap₂ := hg.2.1 }

end
end Candidate.FourthPower.RestoredRootSource
