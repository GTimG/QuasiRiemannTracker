/- Reserve-parametric adaptation by Joseph Bebel (2026). -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Volume and cap geometry for the restored root. The source face supplies
the seed cap, including the range where seedCap N epsilon is below eight.
-/
import Candidate.Local.Qrh.PR98Improvement.RepairedSourceProfiles
import Candidate.Local.Qrh.PR98Improvement.RecenteredRootFamilyDispatch
import Candidate.Local.Qrh.PR98Improvement.RestoredFirstRemainders
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedActualRetained

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.PR98.RepairedSourceRootGeometry
universe u
noncomputable section
open Candidate.FourthPower
variable [Candidate.PR98.RepairedRootParameters.Reserve]
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentUncenteredTerminal
open MixedPrincipalPair MixedOriginalNormCap MixedOriginalTail
open MixedInnerExceptionalBlock
open RestoredRootDictionary RestoredRootEnergy NativeMaskedEnergy
open RepairedRootParameters RecenteredRootSetup RecenteredRootReferenceCaps
open RepairedSourceSideSupply
open QRH.Record1252270103KernelMass
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {α : Type u} [Fintype α]
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem windowCap_ge_eight (N : ℕ) (ε : ℝ) (hε : 0 < ε) : 8 ≤ windowCap N ε := by
  have hm := mul_nonneg (Nat.cast_nonneg N) (mesh_spec ε hε).1.le
  unfold windowCap
  linarith

theorem seedCap_ge_seven (N : ℕ) (ε : ℝ) (hε : 0 < ε) : 7 ≤ seedCap N ε := by
  have hm := mul_nonneg (Nat.cast_nonneg N) (mesh_spec ε hε).1.le
  unfold seedCap
  linarith

theorem root_volume_exact (s : Setup M H α)
    (hn₁ : comparisonScale (9/4) < s.Y₁) (hn₂ : comparisonScale (9/4) < s.Y₂) :
    sourceVolume (s.rootSource hH hn₁ hn₂)=
      s.Z^(ordinaryExponent M H s+markedWidth M H s) := by
  have hz := zero_lt_one.trans s.hZ
  have ht : s.Y₁*s.Y₂=s.Z^(ordinaryExponent M H s) :=
    (Real.rpow_logb hz s.hZ.ne' (mul_pos s.hY₁ s.hY₂)).symm
  change (s.Y₁*s.Y₂)*(∏i,(s.rootSource hH hn₁ hn₂).P i)=_
  rw [root_product M H hH s hn₁ hn₂,ht,←Real.rpow_add hz]

theorem root_logvolume (s : Setup M H α)
    (hn₁ : comparisonScale (9/4) < s.Y₁) (hn₂ : comparisonScale (9/4) < s.Y₂) :
    Real.logb s.Z (sourceVolume (s.rootSource hH hn₁ hn₂))=
      ordinaryExponent M H s+markedWidth M H s := by
  rw [root_volume_exact M H hH s hn₁ hn₂,
    Real.logb_rpow (zero_lt_one.trans s.hZ) s.hZ.ne']

theorem root_volume_le (s : Setup M H α)
    (hn₁ : comparisonScale (9/4) < s.Y₁) (hn₂ : comparisonScale (9/4) < s.Y₂) :
    sourceVolume (s.rootSource hH hn₁ hn₂) ≤ s.Z := by
  have hf := face_volume (actual_face M H s)
  have he : ordinaryExponent M H s+markedWidth M H s ≤ (1:ℝ) := by
    have hr := Candidate.PR98.RepairedRootParameters.Reserve.positive
    dsimp only [rootReserve] at hf
    linarith
  rw [root_volume_exact M H hH s hn₁ hn₂]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le s.hZ.le he

theorem root_norm_sharp (s : Setup M H α)
    (hn₁ : comparisonScale (9/4) < s.Y₁) (hn₂ : comparisonScale (9/4) < s.Y₂)
    (N : ℕ) (hcard : Fintype.card (remainingSet s.r s.A) ≤ N)
    (hconstant : (9/4:ℝ)^2*2^N ≤ s.Z) :
    sourceNormCap (s.rootSource hH hn₁ hn₂).P (9/4)
      (s.rootSource hH hn₁ hn₂).T (s.rootSource hH hn₁ hn₂).d ≤ s.Z^(2:ℝ) := by
  let r := s.rootSource hH hn₁ hn₂
  have hc : (9/4:ℝ)^2*2^Fintype.card (remainingSet s.r s.A) ≤ s.Z :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hcard)
      (sq_nonneg (9/4:ℝ))).trans hconstant
  have he : sourceNormCap r.P (9/4) r.T r.d=
      (9/4:ℝ)^2*2^Fintype.card (remainingSet s.r s.A)*sourceVolume r := by
    rw [MixedActualRetained.sourceNormCap_eq_volume]
    simp only [show r.d=(1,1) from rfl,pairNorm,map_one,Nat.cast_one,mul_one,div_one]
    rfl
  change sourceNormCap r.P (9/4) r.T r.d ≤ s.Z^(2:ℝ)
  rw [he,Real.rpow_two]
  simpa only [pow_two] using mul_le_mul hc (root_volume_le M H hH s hn₁ hn₂)
    (sourceVolume_pos r).le (zero_lt_one.trans s.hZ).le

theorem minimum_cap (Z L ell : ℝ) (hZ : 5 ≤ Z) (hell : 0 ≤ ell)
    (hL : (2/9:ℝ)*Z^ell ≤ L) : Z^(-8:ℝ) ≤ L := by
  have hz : 0 < Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  have hpow : 1 ≤ Z^ell := Real.one_le_rpow hz1 hell
  have hc : (2/9:ℝ) ≤ L := by nlinarith
  calc
    Z^(-8:ℝ) ≤ Z^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
    _ = Z⁻¹ := by rw [Real.rpow_neg_one]
    _ ≤ (5:ℝ)⁻¹ := (inv_le_inv₀ hz (by norm_num)).mpr hZ
    _ ≤ 2/9 := by norm_num
    _ ≤ L := hc

theorem eventual_root_caps (N : ℕ) (ε bΦ : ℝ) (hε : 0 < ε) (hbΦ : 2 ≤ bΦ)
    (η : Character) :
    ∀ᶠ Z : ℝ in atTop, 5 ≤ Z ∧ bΦ ≤ Z ∧ (η.modulus.absNorm:ℝ) ≤ Z ∧
      (9/4:ℝ)^2*2^N ≤ Z ∧
    ∀ (T0 : Finset α) (s : Setup M H T0), s.Z=Z →
    ∀ hn₁ : comparisonScale (9/4) < s.Y₁, ∀ hn₂ : comparisonScale (9/4) < s.Y₂,
      poolCap (s.rootSource hH hn₁ hn₂) ≤ Z^(8:ℝ) ∧
      sourceNormCap (s.rootSource hH hn₁ hn₂).P (9/4)
        (s.rootSource hH hn₁ hn₂).T (s.rootSource hH hn₁ hn₂).d ≤ Z^(8:ℝ) ∧
      sourceVolume (s.rootSource hH hn₁ hn₂) ≤ Z^(8:ℝ) := by
  filter_upwards [RestoredFirstRemainders.root_caps_eventually.{u} M H hH (Fintype.card α) bΦ (by linarith),
    eventually_ge_atTop (5:ℝ),eventually_ge_atTop bΦ,eventually_ge_atTop (η.modulus.absNorm:ℝ),
    eventually_ge_atTop ((9/4:ℝ)^2*2^N)] with Z hc hZ hb hη hdim
  refine ⟨hZ,hb,hη,hdim,?_⟩
  intro T0 s hsZ hn₁ hn₂
  have hcard := root_slot_card (⟨T0,remainingSet s.r s.A⟩ : RootShape α)
  have he := hc.2 (remainingSet s.r s.A) (s.rootData hn₁ hn₂) hcard hsZ (actual_face M H s).2.1
  exact ⟨he.1,he.2.1,he.2.2.1⟩

end
end Candidate.PR98.RepairedSourceRootGeometry
