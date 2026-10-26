/- Copyright (c) 2026 Sil. Apache-2.0.
Canonical geometry after actual fixed-support seed allocation, ordinary
rebasing, and reference replacement. The enclosure is fixed before the
allocation; neither the finite slot holes nor the ambient character grow.
-/
import Candidate.FourthPower.MixedFirstSeededSource
import Candidate.FourthPower.MixedFirstReferenceChoice
import Candidate.FourthPower.MixedFirstActualNonexceptional
import Candidate.FourthPower.MixedFrozenSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstCanonicalGeometry
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass (ideal_norm_one_le)
open CenteredMomentCommonProfile CenteredMomentCommonAllocationBox
open CenteredMomentCommonAllocationSum CenteredMomentUncenteredTerminal
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedFirstLiveSource MixedFirstRebase MixedFirstSeededSource
open MixedFirstReferenceChoice MixedFirstActualNonexceptional
open MixedCanonicalSource MixedFrozenSource MixedLiteralAllocation MixedFixedSupport
open MixedCommonCoefficient MixedCommonRestriction ReferencePrimeEnclosure
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- A fixed choice available before Z, F, B, or the live subset. -/
def enclosureConstant (b : ℝ) : ℝ := max 2 (b/comparisonScale b)

def enclosureExponent (L Lslot : ℝ) : ℝ := max Lslot (2*L+1)

theorem enclosure_exponent_bounds (L Lslot : ℝ) :
    Lslot≤enclosureExponent L Lslot ∧ 2*L+1≤enclosureExponent L Lslot ∧
      2*L≤enclosureExponent L Lslot := by
  refine ⟨le_max_left _ _,le_max_right _ _,?_⟩
  exact (by linarith : 2*L≤2*L+1).trans (le_max_right _ _)

theorem enclosure_constant_bounds (b : ℝ) (hb : 0≤b) :
    2≤enclosureConstant b ∧ b/comparisonScale b≤enclosureConstant b ∧
      b≤enclosureConstant b := by
  have hc := comparisonScale_pos b
  have hc1 : comparisonScale b≤1 := (comparison_scale_le_half b).trans (by norm_num)
  refine ⟨le_max_left _ _,le_max_right _ _,?_⟩
  exact ((le_div_iff₀ hc).mpr (mul_le_of_le_one_right hb hc1)).trans (le_max_right _ _)

theorem seeded_scales_le (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (F : Id) (hF : F≠0) (B : boundedLabels (tuplePools s) F) :
    let r:=seededRebasedSource s hb cover F hF B
    r.X₁≤s.X₁ ∧ r.X₂≤s.X₂ := by
  have hB := (allocation_data (tuplePools s) F B.val (Finset.mem_filter.mp B.property).1).1
  change s.X₁/(s.d.1*B.val (Sum.inr 0)).absNorm≤s.X₁ ∧
    s.X₂/(s.d.2*B.val (Sum.inr 1)).absNorm≤s.X₂
  exact ⟨div_le_self (s.hL.trans_le s.hX₁).le
      (ideal_norm_one_le (mul_ne_zero s.hd.1 (hB _))),
    div_le_self (s.hL.trans_le s.hX₂).le
      (ideal_norm_one_le (mul_ne_zero s.hd.2 (hB _)))⟩

/-- A reference q may be the subunit comparison scale or Z^l. Only its
proved lower floor and its location below the two actual lengths matter. -/
theorem reference_lengths (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (F : Id) (hF : F≠0) (B : boundedLabels (tuplePools s) F)
    (q : ℝ) (hq : comparisonScale b≤q)
    (h₁ : q≤(seededRebasedSource s hb cover F hF B).X₁)
    (h₂ : q≤(seededRebasedSource s hb cover F hF B).X₂) :
    let r:=seededRebasedSource s hb cover F hF B
    0<q ∧ q≤r.T/q ∧ q*(r.T/q)=r.T := by
  let r:=seededRebasedSource s hb cover F hF B
  have hq0 := (comparisonScale_pos b).trans_le hq
  refine ⟨hq0,?_,?_⟩
  · apply (le_div_iff₀ hq0).mpr
    rw [←r.hpX]
    exact mul_le_mul h₁ h₂ hq0.le (hq0.le.trans h₁)
  · field_simp [hq0.ne']

theorem centered_reference_floor (b Z l : ℝ) (hZ : 1≤Z) (hl : 0≤l) :
    comparisonScale b≤Z^l :=
  (comparison_scale_le_half b).trans ((by norm_num : (1/2:ℝ)≤1).trans (Real.one_le_rpow hZ hl))

/-- All four reference bounds use ONE C=Cap*Z^Lcap selected before F/B.
The full puncture R*F is not put into R0 and no hole count is enlarged. -/
theorem reference_enclosure_caps (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (F : Id) (hF : F≠0)
    (B : boundedLabels (tuplePools s) F) (Z L Lcap Cap q : ℝ)
    (hZ : 1≤Z) (hL : 0≤L) (hLc : 2*L≤Lcap)
    (hCap : b/comparisonScale b≤Cap) (hX₁ : s.X₁≤Z^L) (hX₂ : s.X₂≤Z^L)
    (hq : comparisonScale b≤q)
    (hq₁ : q≤(seededRebasedSource s hb cover F hF B).X₁) :
    let r:=seededRebasedSource s hb cover F hF B
    b*r.X₁≤Cap*Z^Lcap ∧ b*r.X₂≤Cap*Z^Lcap ∧
      b*q≤Cap*Z^Lcap ∧ b*(r.T/q)≤Cap*Z^Lcap := by
  let r:=seededRebasedSource s hb cover F hF B
  have hz := zero_lt_one.trans_le hZ
  have hc := comparisonScale_pos b
  have hq0 := hc.trans_le hq
  have hc1 : comparisonScale b≤1 := (comparison_scale_le_half b).trans (by norm_num)
  have hbCap : b≤Cap := ((le_div_iff₀ hc).mpr (mul_le_of_le_one_right hb hc1)).trans hCap
  have hCap0 : 0≤Cap := hb.trans hbCap
  have hs := seeded_scales_le s hb cover F hF B
  have hr₁ : r.X₁≤Z^L := hs.1.trans hX₁
  have hr₂ : r.X₂≤Z^L := hs.2.trans hX₂
  have hpower : Z^L≤Z^Lcap := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hh₁ : b*r.X₁≤Cap*Z^Lcap := mul_le_mul hbCap (hr₁.trans hpower)
    (r.hL.trans_le r.hX₁).le hCap0
  have hh₂ : b*r.X₂≤Cap*Z^Lcap := mul_le_mul hbCap (hr₂.trans hpower)
    (r.hL.trans_le r.hX₂).le hCap0
  have hT : r.T≤Z^(2*L) := by
    rw [←r.hpX]
    calc
      _≤Z^L*Z^L := mul_le_mul hr₁ hr₂ (r.hL.trans_le r.hX₂).le (Real.rpow_nonneg hz.le _)
      _=Z^(2*L) := by rw [←Real.rpow_add hz];congr 1;ring
  refine ⟨hh₁,hh₂,(mul_le_mul_of_nonneg_left hq₁ hb).trans hh₁,?_⟩
  calc
    b*(r.T/q)≤b*(Z^(2*L)/comparisonScale b) :=
      mul_le_mul_of_nonneg_left
        ((div_le_div_of_nonneg_left r.total_pos.le hc hq).trans
          (div_le_div_of_nonneg_right hT hc.le)) hb
    _=(b/comparisonScale b)*Z^(2*L) := by ring
    _≤Cap*Z^Lcap := mul_le_mul hCap (Real.rpow_le_rpow_of_exponent_le hZ hLc)
      (Real.rpow_nonneg hz.le _) hCap0

/-- The inverse subunit reference floor is a fixed constant. One
eventual threshold before all sources yields a literal pure-power cap. -/
theorem eventually_reference_power_caps (b L : ℝ) (hL : 0≤L) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,∀hb : 0≤b,
    ∀cover : OriginalEnclosure s,∀F : Id,∀hF : F≠0,
    ∀B : boundedLabels (tuplePools s) F,
      s.X₁≤Z^L→s.X₂≤Z^L→∀q : ℝ,comparisonScale b≤q→
      q≤(seededRebasedSource s hb cover F hF B).X₁→
      let r:=seededRebasedSource s hb cover F hF B
      r.X₁≤Z^(2*L+1) ∧ r.X₂≤Z^(2*L+1) ∧
        q≤Z^(2*L+1) ∧ r.T/q≤Z^(2*L+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop ((comparisonScale b)⁻¹)] with Z hZ hfixed
  refine ⟨hZ,?_⟩
  intro ι instι a s hb cover F hF B hX₁ hX₂ q hq hq₁ r
  have hz := zero_lt_one.trans hZ
  have hc := comparisonScale_pos b
  have hs := seeded_scales_le s hb cover F hF B
  have hr₁ : r.X₁≤Z^L := hs.1.trans hX₁
  have hr₂ : r.X₂≤Z^L := hs.2.trans hX₂
  have hh : Z^L≤Z^(2*L+1) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hT : r.T≤Z^(2*L) := by
    rw [←r.hpX]
    calc
      _≤Z^L*Z^L := mul_le_mul hr₁ hr₂ (r.hL.trans_le r.hX₂).le (Real.rpow_nonneg hz.le _)
      _=Z^(2*L) := by rw [←Real.rpow_add hz];congr 1;ring
  refine ⟨hr₁.trans hh,hr₂.trans hh,hq₁.trans (hr₁.trans hh),?_⟩
  calc
    _≤Z^(2*L)/comparisonScale b := (div_le_div_of_nonneg_left r.total_pos.le hc hq).trans
      (div_le_div_of_nonneg_right hT hc.le)
    _≤Z^(2*L)*Z := by rw [div_eq_mul_inv];exact mul_le_mul_of_nonneg_left hfixed (Real.rpow_nonneg hz.le _)
    _=Z^(2*L+1) := by rw [Real.rpow_add hz,Real.rpow_one]

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem seeded_canonical (W : ℝ→ℂ) (Cap Lcap Z : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s)
    (hb : 0≤b) (cover : OriginalEnclosure s) (F : Id) (hF : F≠0)
    (B : boundedLabels (tuplePools s) F) :
    Canonical M Hray hHray W Cap Lcap Z η₀
      (fun i : liveIndices B.val=>θ i.val) (fun i=>w i.val)
      (fun i=>σ i.val) (fun i=>freq i.val) t (fun i=>R₀ i.val)
      (seededRebasedSource s hb cover F hF B) := by
  obtain ⟨hS,hpool,hν,hW,hP⟩ := hs
  refine ⟨hS,?_,?_,?_,?_⟩
  · change (fun i : liveIndices B.val=>s.pool i.val)=_
    simpa only [hpool]
  · change (fun i : liveIndices B.val=>s.ν i.val)=_
    rw [hν]
    rfl
  · change (fun i : liveIndices B.val=>s.Wslot i.val)=_
    simpa only [hW]
  · change (fun i : liveIndices B.val=>s.P i.val)=_
    simpa only [hP]

/-- The actual constructor, not a premise that a new reference source
already exists. The same enclosure and R0 are used for every allocation. -/
def allocatedReference (W : ℝ→ℂ) (Cap Lcap Z L : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s)
    (hb : 0≤b) (cover : OriginalEnclosure s) (F : Id) (hF : F≠0)
    (B : boundedLabels (tuplePools s) F) (q : ℝ)
    (hZ : 1≤Z) (hL : 0≤L) (hLc : 2*L≤Lcap)
    (hCap : b/comparisonScale b≤Cap) (hX₁ : s.X₁≤Z^L) (hX₂ : s.X₂≤Z^L)
    (hq : comparisonScale b≤q)
    (hq₁ : q≤(seededRebasedSource s hb cover F hF B).X₁)
    (hq₂ : q≤(seededRebasedSource s hb cover F hF B).X₂) :
    Source (liveIndices B.val) a b := by
  let r:=seededRebasedSource s hb cover F hF B
  have hlen:=reference_lengths s hb cover F hF B q hq hq₁ hq₂
  have hcaps:=reference_enclosure_caps s hb cover F hF B Z L Lcap Cap q
    hZ hL hLc hCap hX₁ hX₂ hq hq₁
  have hprimes : ∀Q∈r.S,(Q.val.absNorm:ℝ)≤Cap*Z^Lcap := by
    intro Q hQ
    change Q∈s.S at hQ
    rw [hs.1] at hQ
    exact (enclosure_bound _ Q hQ).2
  exact canonicalReferenceSource r hb q (r.T/q) q hlen.1 hq₁ hq₂ le_rfl hlen.2.1 hlen.2.2
    (Cap*Z^Lcap) hprimes hcaps.1 hcaps.2.1 hcaps.2.2.1 hcaps.2.2.2

theorem allocated_reference_data (W : ℝ→ℂ) (Cap Lcap Z L : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s)
    (hb : 0≤b) (cover : OriginalEnclosure s) (F : Id) (hF : F≠0)
    (B : boundedLabels (tuplePools s) F) (q : ℝ)
    (hZ : 1≤Z) (hL : 0≤L) (hLc : 2*L≤Lcap)
    (hCap : b/comparisonScale b≤Cap) (hX₁ : s.X₁≤Z^L) (hX₂ : s.X₂≤Z^L)
    (hq : comparisonScale b≤q)
    (hq₁ : q≤(seededRebasedSource s hb cover F hF B).X₁)
    (hq₂ : q≤(seededRebasedSource s hb cover F hF B).X₂) :
    let r:=allocatedReference M Hray hHray W Cap Lcap Z L η₀ θ w σ freq t R₀ s hs hb cover
      F hF B q hZ hL hLc hCap hX₁ hX₂ hq hq₁ hq₂
    Canonical M Hray hHray W Cap Lcap Z η₀ (fun i : liveIndices B.val=>θ i.val)
      (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val) t (fun i=>R₀ i.val) r ∧
      r.d=(1,1) ∧ r.B=(fun _=>1) ∧ r.G=1 ∧ r.R=s.R*F ∧
      r.H=s.S.filter (fun Q=>Q∈s.H) ∧ r.Fhole=s.Fhole ∧
      r.M=(fun i : liveIndices B.val=>s.M i.val) ∧ r.L=q ∧
      r.Y₁=q ∧ r.Y₂=(seededRebasedSource s hb cover F hF B).T/q ∧
      OriginalEnclosure r := by
  intro r
  have hc:=seeded_canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s hs hb cover F hF B
  have hcanonical : Canonical M Hray hHray W Cap Lcap Z η₀
      (fun i : liveIndices B.val=>θ i.val) (fun i=>w i.val)
      (fun i=>σ i.val) (fun i=>freq i.val) t (fun i=>R₀ i.val) r :=
    ⟨rfl,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2⟩
  refine ⟨hcanonical,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro I hI hlen
  apply r.henclose I hI
  simpa only [show r.B=(fun _=>1) from rfl,mul_one] using hlen

/-- This is the exact finite-hole condition after restriction. The new
full puncture s.R*F stays in R and does not enter the hole cardinality. -/
theorem restricted_holes (s : Source ι a b) (R₀ : ι→Finset Id) (Holes : ℕ)
    (hcard : ∀i,(R₀ i).card≤Holes) (hHR : ∀i,∀Q∈s.H,Q.val∈R₀ i)
    (B : CenteredMomentAddedZeroUniform.Tuple ι) :
    (∀i : liveIndices B,(R₀ i.val).card≤Holes) ∧
      (∀i : liveIndices B,∀Q∈s.S.filter (fun Q=>Q∈s.H),Q.val∈R₀ i.val) :=
  ⟨fun i=>hcard i.val,fun i Q hQ=>hHR i.val Q (Finset.mem_filter.mp hQ).2⟩

theorem active_holes_enclosed (s : Source ι a b) (C : ℝ) (hs : s.S=enclosure C) :
    s.S.filter (fun Q=>Q∈s.H)⊆enclosure C := by
  intro Q hQ
  rw [←hs]
  exact (Finset.mem_filter.mp hQ).1

/-- The full new puncture is paid as a product of full norms; no radical
is substituted for F and no bound on its prime-support cardinality is used. -/
theorem seeded_puncture_cap (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (F : Id) (hF : F≠0) (B : boundedLabels (tuplePools s) F)
    (Z BR BF : ℝ) (hZ : 0<Z)
    (hR : (s.R.absNorm:ℝ)≤Z^BR) (hFcap : (F.absNorm:ℝ)≤Z^BF) :
    ((seededRebasedSource s hb cover F hF B).R.absNorm:ℝ)≤Z^(BR+BF) := by
  change ((s.R*F).absNorm:ℝ)≤Z^(BR+BF)
  rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
  exact mul_le_mul hR hFcap (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

/-- Store the uniform slot bound as actual Source data. This changes no
pool, coefficient, height, puncture or scale, and can precede allocation. -/
def recapSlots (s : Source ι a b) (K : ℝ) (hK : 1≤K)
    (hbound : ∀i x,‖s.Wslot i x‖≤K) : Source ι a b :=
  {s with M:=fun _=>K,hM:=fun _=>hK,hWnorm:=hbound}

theorem recap_coefficient (s : Source ι a b) (K : ℝ) (hK : 1≤K)
    (hbound : ∀i x,‖s.Wslot i x‖≤K) (ha : 0<a) (seed : Id) :
    sourceCoefficient (recapSlots s K hK hbound) ha seed=sourceCoefficient s ha seed := rfl

theorem uniform_canonical_slot_bound (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (lo hi : ℝ) :
    ∃K : ℝ,1≤K ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
    ∀σ freq : ι→ℝ,s.Wslot=(fun i=>MixedCanonicalSource.slotProfile W (σ i) (freq i))→
      (∀i,lo≤σ i)→(∀i,σ i≤hi)→∀i x,‖s.Wslot i x‖≤K := by
  obtain ⟨K,hK,hbound⟩:=slot_profile_bound W hW hWs lo hi
  refine ⟨K,hK,?_⟩
  intro ι instι a b s σ freq hs hlo hhi i x
  rw [hs]
  exact hbound (σ i) (freq i) (hlo i) (hhi i) x

end
end Candidate.FourthPower.MixedFirstCanonicalGeometry
