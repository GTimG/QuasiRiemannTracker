/- Copyright (c) 2026 Sil. Apache-2.0.
Constructors for the shared RootInput, using structural root data.
The low and centered roots retain their actual length, and the adaptive
exponent is chosen before the first allocations.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedSourceRootGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSourceRootInput
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentUncenteredTerminal
open MixedPrincipalPair MixedPrincipalAllocations MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open RestoredRootDictionary RestoredRootEnergy NativeMaskedEnergy
open RepairedRootParameters RepairedRawContext RecenteredRootSetup RecenteredRootSource
open RecenteredRootReferenceCaps RepairedSourceSideSupply RepairedSourceRootGeometry
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {α : Type u} [Fintype α]
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable (ε : ℝ) (hε : 0 < ε) (T0 : Finset α) (s : Setup M H T0)
variable (hLc : s.Lcap=windowCap (Fintype.card α) ε)
variable (V bΦ : ℝ) (hV : 0 ≤ V) (hbΦ : 2 ≤ bΦ)
variable (hfreq : ∀i,|s.v i| ≤ V) (hwm : ∀i,s.w i ≤ mesh ε)
variable (η : Character) (hZ5 : 5 ≤ s.Z) (hbZ : bΦ ≤ s.Z)
variable (hη : (η.modulus.absNorm:ℝ) ≤ s.Z)
variable (hdim : (9/4:ℝ)^2*2^(Fintype.card α) ≤ s.Z)
variable (hn₁ : comparisonScale (9/4) < s.Y₁) (hn₂ : comparisonScale (9/4) < s.Y₂)
variable (hpool : poolCap (s.rootSource hH hn₁ hn₂) ≤ s.Z^(8:ℝ))

theorem actual_holes_card :
    (restorationHoles s.r (RestoredInitialSource.primeEnclosure s.Z) s.tc s.A s.ti).card ≤
      2*Fintype.card α :=
  (restoration_holes_card s.r _ s.tc s.A s.ti).trans
    (Nat.mul_le_mul_left 2 (Fintype.card_le_of_injective (fun i : T0 => i.val) Subtype.val_injective))

include hε hdim in
theorem actual_sharp_seed_cap :
    sourceNormCap (s.rootSource hH hn₁ hn₂).P (9/4)
      (s.rootSource hH hn₁ hn₂).T (s.rootSource hH hn₁ hn₂).d ≤
      s.Z^(seedCap (Fintype.card α) ε) := by
  apply (root_norm_sharp M H hH s hn₁ hn₂ (Fintype.card α)
    (root_slot_card (⟨T0,remainingSet s.r s.A⟩ : RootShape α)) hdim).trans
  exact Real.rpow_le_rpow_of_exponent_le s.hZ.le
    (by linarith only [seedCap_ge_seven (Fintype.card α) ε hε])

include hbΦ hbZ in
theorem actual_radial_caps : s.Z ≤ bΦ*s.Z ∧ bΦ*s.Z ≤ s.Z^(2:ℝ) := by
  have hz := zero_lt_one.trans s.hZ
  constructor
  · nlinarith only [hbΦ,hz]
  · simpa only [Real.rpow_two,pow_two] using mul_le_mul_of_nonneg_right hbZ hz.le

set_option maxHeartbeats 800000 in
def lowInput
    (hlow : ¬NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s)) :
    RootInput M H hH (remainingSet s.r s.A) s.W (Fintype.card α) (2*Fintype.card α)
      ε s.Z (RestoredRootSource.slotBound s.W s.hW s.hWs) η s.η₀ where
  root := s.rootSource hH hn₁ hn₂
  cover := (s.rootData hn₁ hn₂).source_original_enclosure hH
  chars := fun i => s.θ i.val
  w := fun i => s.w i.val
  freq := fun i => s.v i.val
  t₀ := s.t
  V := V
  ell := 0
  Kroot := bΦ*s.Z
  R₀ := fun _ => restorationHoles s.r (RestoredInitialSource.primeEnclosure s.Z) s.tc s.A s.ti
  hZ := hZ5
  hw := fun i => s.hw i.val
  hwm := fun i => hwm i.val
  hV := hV
  hfreq := fun i => hfreq i.val
  hholes := fun _ => actual_holes_card M H T0 s
  hcanonical := by
    rw [← hLc]
    exact (s.rootData hn₁ hn₂).source_canonical hH
  hM := fun _ => le_rfl
  hunit := rfl
  hR := rfl
  hH := rfl
  hF := rfl
  hX₁ := ((s.rootData hn₁ hn₂).source_length_caps hH hZ5).1
  hX₂ := ((s.rootData hn₁ hn₂).source_length_caps hH hZ5).2.1
  hY₁ := ((s.rootData hn₁ hn₂).source_length_caps hH hZ5).2.2.1
  hY₂ := ((s.rootData hn₁ hn₂).source_length_caps hH hZ5).2.2.2
  hnorm := actual_sharp_seed_cap M H hH ε hε T0 s hdim hn₁ hn₂
  hpool := hpool
  hface := actual_face M H s
  hell := le_rfl
  hminimum := by
    change (2/9:ℝ)*s.Z^(0:ℝ) ≤ comparisonScale (9/4)
    norm_num [comparisonScale]
  hmargin := by
    rw [root_logvolume M H hH s hn₁ hn₂]
    simpa only [mul_zero,zero_div,sub_zero] using low_exceptional_margin hlow
  hKlow := (actual_radial_caps M H T0 s bΦ hbΦ hbZ).1
  hKcap := (actual_radial_caps M H T0 s bΦ hbΦ hbZ).2
  hη := hη

set_option maxHeartbeats 1000000 in
def highInput
    (hhigh : NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s))
    (h₁ : rootReference M H s ε ≤ s.Y₁) (h₂ : rootReference M H s ε ≤ s.Y₂) :
    RootInput M H hH (remainingSet s.r s.A) s.W (Fintype.card α) (2*Fintype.card α)
      ε s.Z (RestoredRootSource.slotBound s.W s.hW s.hWs) η s.η₀ where
  root := centeredRoot M H hH s ε hε hn₁ hn₂ hhigh h₁ h₂
  cover := (s.rootData hn₁ hn₂).source_original_enclosure hH
  chars := fun i => s.θ i.val
  w := fun i => s.w i.val
  freq := fun i => s.v i.val
  t₀ := s.t
  V := V
  ell := rootExponent M H s ε
  Kroot := bΦ*s.Z
  R₀ := fun _ => restorationHoles s.r (RestoredInitialSource.primeEnclosure s.Z) s.tc s.A s.ti
  hZ := hZ5
  hw := fun i => s.hw i.val
  hwm := fun i => hwm i.val
  hV := hV
  hfreq := fun i => hfreq i.val
  hholes := fun _ => actual_holes_card M H T0 s
  hcanonical := by
    simpa only [hLc] using centeredRoot_canonical M H hH s ε hε hn₁ hn₂ hhigh h₁ h₂
  hM := fun _ => le_rfl
  hunit := rfl
  hR := rfl
  hH := rfl
  hF := rfl
  hX₁ := ((s.rootData hn₁ hn₂).source_length_caps hH hZ5).1
  hX₂ := ((s.rootData hn₁ hn₂).source_length_caps hH hZ5).2.1
  hY₁ := h₁.trans ((s.rootData hn₁ hn₂).source_length_caps hH hZ5).1
  hY₂ := (reference_second_le (s.rootSource hH hn₁ hn₂) (rootReference M H s ε)
    (reference_geometry M H s ε hε hhigh).1
    (reference_geometry M H s ε hε hhigh).2.2.1).trans
      ((s.rootData hn₁ hn₂).source_length_caps hH hZ5).2.2.2
  hnorm := actual_sharp_seed_cap M H hH ε hε T0 s hdim hn₁ hn₂
  hpool := (recenter_poolCap_le (s.rootSource hH hn₁ hn₂) (rootReference M H s ε)
    (reference_geometry M H s ε hε hhigh).1
    (reference_geometry M H s ε hε hhigh).2.2.1 h₁ h₂).trans hpool
  hface := actual_face M H s
  hell := (reference_geometry M H s ε hε hhigh).2.2.2.2.1.le
  hminimum := by
    change (2/9:ℝ)*s.Z^(rootExponent M H s ε) ≤ s.Z^(rootExponent M H s ε)
    exact mul_le_of_le_one_left (Real.rpow_nonneg (zero_lt_one.trans s.hZ).le _) (by norm_num)
  hmargin := by
    change Real.logb s.Z (sourceVolume (s.rootSource hH hn₁ hn₂))-
      5/6-2*rootExponent M H s ε/3 ≤ -10*omegaLoss ε
    rw [root_logvolume M H hH s hn₁ hn₂]
    have he := centered_exceptional_margin hε (actual_face M H s) hhigh
    dsimp only [rootExponent]
    nlinarith only [he]
  hKlow := (actual_radial_caps M H T0 s bΦ hbΦ hbZ).1
  hKcap := (actual_radial_caps M H T0 s bΦ hbΦ hbZ).2
  hη := hη

end
end Candidate.FourthPower.RepairedSourceRootInput
