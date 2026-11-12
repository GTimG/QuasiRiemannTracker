/- Copyright (c) 2026 Sil. Apache-2.0.
Volume and cap geometry for the restored root. The source face supplies
the seed cap, including the range where seedCap N epsilon is below eight.
Modified by Sil (2026-10-26): over Setup M H D and the gates G (windowCap/seedCap/mesh G); root_volume_le uses the new root_face_budget (P + L S <= B without the lower end s0) and root_exponent_le_one (L > 1, B < 1) instead of FP face_volume; eventual_root_caps uses marked_width_cap and c <= 1/6 (Setup.hD); the import of RecenteredRootFamilyDispatch is kept.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceRootGeometry`; `root_exponent_le_one` uses the volume
gate `StepGates.volume` in place of `1 < L`.
-/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceProfiles
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootFamilyDispatch
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RestoredFirstRemainders
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedActualRetained

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceRootGeometry
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentUncenteredTerminal
open MixedPrincipalPair MixedOriginalNormCap MixedOriginalTail
open MixedInnerExceptionalBlock
open RestoredRootDictionary RestoredRootEnergy NativeMaskedEnergy
open Qrh.MarkedAnchor.Ordinary.RootParameters RecenteredRootSetup RecenteredRootReferenceCaps
open RepairedSourceSideSupply
open QRH.Record1252270103KernelMass QRH.Record1252270103Source CenteredMomentEnergyBands
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqRootGeometry {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {α : Type u} [Fintype α]
variable {D : StepData} (G : StepGates D)
variable (M : Id) [NeZero M]
local instance instFiniteQuotRootGeometry : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem windowCap_ge_eight (N : ℕ) (ε : ℝ) (hε : 0 < ε) : 8 ≤ windowCap G N ε := by
  have hm := mul_nonneg (Nat.cast_nonneg N) (mesh_spec G ε hε).1.le
  unfold windowCap
  linarith

theorem seedCap_ge_seven (N : ℕ) (ε : ℝ) (hε : 0 < ε) : 7 ≤ seedCap G N ε := by
  have hm := mul_nonneg (Nat.cast_nonneg N) (mesh_spec G ε hε).1.le
  unfold seedCap
  linarith

/-- The root face without its lower end: `P + L·S ≤ B` for the surviving marked width
(the third component of `RecenteredRootSetup.actual_face`, which needs no `s₀ ≤ S`). -/
theorem root_face_budget (s : Setup M H D α) :
    ordinaryExponent M H s + D.L*markedWidth M H s ≤ D.B := by
  have hs:0≤∑i,s.w i:=Finset.sum_nonneg (fun i _=>s.hw i)
  obtain ⟨-,hbudget⟩:=(globalFace_admissible_iff
    (length_nonneg s.Z s.X₁ s.hZ) (length_nonneg s.Z s.X₂ s.hZ) hs
    s.hD.2.1).mp s.hface
  simp only [mul_one] at hbudget
  have hsub:(∑i:remainingSet s.r s.A,s.w i.val)≤∑i,s.w i := by
    rw [Finset.sum_coe_sort (remainingSet s.r s.A) s.w]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>s.hw i)
  have hlog₁:Real.logb s.Z s.Y₁≤length s.Z s.X₁:=
    Real.logb_le_logb_of_le s.hZ s.hY₁ (s.hy₁.trans (le_max_right _ _))
  have hlog₂:Real.logb s.Z s.Y₂≤length s.Z s.X₂:=
    Real.logb_le_logb_of_le s.hZ s.hY₂ (s.hy₂.trans (le_max_right _ _))
  have hLsub:D.L*(∑i:remainingSet s.r s.A,s.w i.val)≤D.L*(∑i,s.w i):=
    mul_le_mul_of_nonneg_left hsub s.hD.2.1
  dsimp only [ordinaryExponent,markedWidth]
  rw [Real.logb_mul s.hY₁.ne' s.hY₂.ne']
  linarith

include G in
/-- `P + S ≤ 1` at the root (the face budget and the volume gate `StepGates.volume`). -/
theorem root_exponent_le_one (s : Setup M H D α) :
    ordinaryExponent M H s+markedWidth M H s ≤ 1 := by
  have h := root_face_budget M H s
  have hS : 0 ≤ markedWidth M H s := Finset.sum_nonneg (fun i _ => s.hw _)
  have hv := G.volume hS (marked_width_cap M H s)
  have hρ := G.reference_spec.1
  nlinarith

theorem root_volume_exact (s : Setup M H D α)
    (hn₁ : comparisonScale (9/4) < s.Y₁) (hn₂ : comparisonScale (9/4) < s.Y₂) :
    sourceVolume (s.rootSource hH hn₁ hn₂)=
      s.Z^(ordinaryExponent M H s+markedWidth M H s) := by
  have hz := zero_lt_one.trans s.hZ
  have ht : s.Y₁*s.Y₂=s.Z^(ordinaryExponent M H s) :=
    (Real.rpow_logb hz s.hZ.ne' (mul_pos s.hY₁ s.hY₂)).symm
  change (s.Y₁*s.Y₂)*(∏i,(s.rootSource hH hn₁ hn₂).P i)=_
  rw [root_product M H hH s hn₁ hn₂,ht,←Real.rpow_add hz]

theorem root_logvolume (s : Setup M H D α)
    (hn₁ : comparisonScale (9/4) < s.Y₁) (hn₂ : comparisonScale (9/4) < s.Y₂) :
    Real.logb s.Z (sourceVolume (s.rootSource hH hn₁ hn₂))=
      ordinaryExponent M H s+markedWidth M H s := by
  rw [root_volume_exact M H hH s hn₁ hn₂,
    Real.logb_rpow (zero_lt_one.trans s.hZ) s.hZ.ne']

include G in
theorem root_volume_le (s : Setup M H D α)
    (hn₁ : comparisonScale (9/4) < s.Y₁) (hn₂ : comparisonScale (9/4) < s.Y₂) :
    sourceVolume (s.rootSource hH hn₁ hn₂) ≤ s.Z := by
  have he : ordinaryExponent M H s+markedWidth M H s ≤ (1:ℝ) := root_exponent_le_one G M H s
  rw [root_volume_exact M H hH s hn₁ hn₂]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le s.hZ.le he

include G in
theorem root_norm_sharp (s : Setup M H D α)
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
  simpa only [pow_two] using mul_le_mul hc (root_volume_le G M H hH s hn₁ hn₂)
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
    ∀ (T0 : Finset α) (s : Setup M H D T0), s.Z=Z →
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
  have he := hc.2 (remainingSet s.r s.A) (s.rootData hn₁ hn₂) hcard hsZ ((marked_width_cap M H s).trans s.hD.2.2)
  exact ⟨he.1,he.2.1,he.2.2.1⟩

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedSourceRootGeometry
