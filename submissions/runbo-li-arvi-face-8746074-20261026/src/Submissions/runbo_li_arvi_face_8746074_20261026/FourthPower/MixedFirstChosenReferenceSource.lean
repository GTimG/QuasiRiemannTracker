/- Copyright (c) 2026 Sil. Apache-2.0.
The actual allocated reference uses the LIVE total and LIVE marked width.
Short original factors are not silently assigned a longer reference.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstCanonicalGeometry
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstChosenEnergy

set_option autoImplicit false
namespace Candidate.FourthPower.MixedFirstChosenReferenceSource
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonProfile CenteredMomentUncenteredTerminal
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstSeededSource MixedFirstCanonicalGeometry MixedFirstActualNonexceptional
open MixedFirstReferenceChoice MixedFirstChosenEnergy MixedFirstPaidCosts
open MixedFirstGeometricCaps MixedInnerExceptionalBlock MixedFixedSupport
open QRH.Record1252270103KernelMass (pairNorm)
local notation "Id" => Ideal HeckeFamily.O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def qReference (b Z R P S d : ℝ) : ℝ :=
  if P+S ≤ 5*R/6-7*d/3 then comparisonScale b
  else Z^(referenceExponent R P S d)

/-- The uncentered length is c, whereas its exponent is zero. The
centered length is Z^l. The same cstar=c works in both physical branches. -/
theorem reference_length_geometry (b Z R P S d : ℝ)
    (hZ : 1 ≤ Z) (hmix : P+2*S+4*d < R) :
    let q := qReference b Z R P S d
    let l := referenceExponent R P S d
    comparisonScale b ≤ q ∧ 0 < q ∧ comparisonScale b*Z^l ≤ q ∧
      0 ≤ l ∧ q ≤ Z^l := by
  have hc : 0 < comparisonScale b := comparisonScale_pos b
  have hc1 : comparisonScale b ≤ 1 :=
    (comparison_scale_le_half b).trans (by norm_num)
  have hl := (reference_choice_bounds (reference_exponent_choice R P S d hmix)).1
  dsimp only
  by_cases h : P+S ≤ 5*R/6-7*d/3
  · simp only [qReference,referenceExponent,h,ite_true,Real.rpow_zero,mul_one]
    exact ⟨le_refl _,hc,le_refl _,le_refl _,hc1⟩
  · rw [qReference,if_neg h]
    refine ⟨centered_reference_floor b Z _ hZ hl,
      Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _,?_,hl,le_refl _⟩
    exact mul_le_of_le_one_left (Real.rpow_nonneg (zero_le_one.trans hZ) _) hc1

/-- A centered actual source with minimum length >=1 automatically has
sharpSupport>=1. The marked product bound comes from Source.hP itself. -/
theorem unit_source_sharp_support (s : Source ι a b)
    (hb : 1 ≤ b) (hunit : s.d=(1,1)) (hL : 1 ≤ s.L) :
    1 ≤ sharpSupport s := by
  have hX₁ : 1 ≤ s.X₁ := hL.trans s.hX₁
  have hX₂ : 1 ≤ s.X₂ := hL.trans s.hX₂
  have hslots : 1 ≤ ∏ i, s.P i := Finset.one_le_prod₀ (fun i _ => s.hP i)
  have hv : 1 ≤ sourceVolume s :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hX₁ hX₂) hslots
  have hconstant : 1 ≤ supportConstant b (Fintype.card ι) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hb)
      (one_le_pow₀ (one_le_pow₀ (by norm_num)))
  rw [sharp_support_eq,hunit]
  simp only [pairNorm,map_one,Nat.cast_one,mul_one,div_one]
  exact one_le_mul_of_one_le_of_one_le hconstant hv

/-- The complementary support branch is exactly zero, even for subunit
uncentered sources. It must not be replaced by a false lower support cap. -/
theorem below_unit_source_zero (s : Source ι a b) (ha : 0 < a)
    (hsmall : sharpSupport s < 1) (seed I : Id) : sourceCoefficient s ha seed I = 0 := by
  by_contra hn
  exact (not_le.mpr hsmall) (sharp_support_one_le s ha seed I hn)

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (HeckeFamily.O⧸M)ˣ)
  (hHray : RayOrthogonality.globalUnits M ≤ Hray)

/-- Instantiate the EXISTING actual allocatedReference constructor at
the choice made after seed allocation and ordinary rebasing. Its two
length premises deliberately remain explicit: otherwise the short-left
or short-right source is handled by ReferenceEnergy instead.

The final length inequality is exactly the remaining ChosenEnergy
premise, computed using the new source's T and the SAME live width sum. -/
theorem allocated_chosen_data
    (W : ℝ→ℂ) (Cap Lcap Z L : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s)
    (hb : 0 ≤ b) (cover : OriginalEnclosure s) (F : Id) (hF : F ≠ 0)
    (B : boundedLabels (tuplePools s) F) (R d : ℝ)
    (hZ : 1 ≤ Z) (hL : 0 ≤ L) (hLc : 2*L ≤ Lcap)
    (hCap : b/comparisonScale b ≤ Cap) (hX₁ : s.X₁ ≤ Z^L) (hX₂ : s.X₂ ≤ Z^L) :
    let live := seededRebasedSource s hb cover F hF B
    let P := Real.logb Z live.T
    let S := ∑ i : liveIndices B.val, w i.val
    ∀ hmix : P+2*S+4*d < R,
    let q := qReference b Z R P S d
    let hfloor := (reference_length_geometry b Z R P S d hZ hmix).1
    ∀ hq₁ : q ≤ live.X₁, ∀ hq₂ : q ≤ live.X₂,
    let r := allocatedReference M Hray hHray W Cap Lcap Z L η₀ θ w σ freq t R₀ s hs
      hb cover F hF B q hZ hL hLc hCap hX₁ hX₂ hfloor hq₁ hq₂
    Canonical M Hray hHray W Cap Lcap Z η₀ (fun i : liveIndices B.val => θ i.val)
      (fun i => w i.val) (fun i => σ i.val) (fun i => freq i.val) t (fun i => R₀ i.val) r ∧
    r.d=(1,1) ∧ r.L=q ∧ r.T=live.T ∧ r.P=live.P ∧
    sourceVolume r=sourceVolume live ∧
    referenceExponent R (Real.logb Z r.T) S d=referenceExponent R P S d ∧
    comparisonScale b*Z^(referenceExponent R (Real.logb Z r.T) S d) ≤ r.L ∧
    comparisonScale b ≤ r.L ∧
    (1 ≤ b → 5*R/6-7*d/3 < P+S → 1 ≤ sharpSupport r) ∧
    (∀ ha : 0 < a, sharpSupport r < 1 → ∀ seed I : Id, sourceCoefficient r ha seed I=0) := by
  intro live P S hmix q hfloor hq₁ hq₂ r
  have hdata := allocated_reference_data M Hray hHray W Cap Lcap Z L η₀ θ w σ freq t R₀
    s hs hb cover F hF B q hZ hL hLc hCap hX₁ hX₂ hfloor hq₁ hq₂
  rcases hdata with ⟨hcanonical,hunit,hB,hG,hR,hH,hFhole,hM,hLr,hY₁,hY₂,hcover⟩
  have hT : r.T=live.T := rfl
  have hgeo := reference_length_geometry b Z R P S d hZ hmix
  have hchosen : comparisonScale b*Z^(referenceExponent R (Real.logb Z r.T) S d) ≤ r.L := by
    rw [hT,hLr]
    exact hgeo.2.2.1
  refine ⟨hcanonical,hunit,hLr,hT,rfl,rfl,rfl,hchosen,?_,?_,?_⟩
  · rw [hLr]
    exact hfloor
  · intro hb1 hcenter
    apply unit_source_sharp_support r hb1 hunit
    rw [hLr]
    change 1 ≤ qReference b Z R P S d
    rw [qReference,if_neg (not_le.mpr hcenter)]
    exact Real.one_le_rpow hZ hgeo.2.2.2.1
  · intro ha hsmall seed I
    exact below_unit_source_zero r ha hsmall seed I

end
end Candidate.FourthPower.MixedFirstChosenReferenceSource
