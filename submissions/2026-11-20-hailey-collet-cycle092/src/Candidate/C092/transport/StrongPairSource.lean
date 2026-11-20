/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairAt

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM  ≤  Hr)

/-- This keeps two authentic fixed anchors and both exceptional exclusions.
The cap ordering labels whole ordinary tuples; it does not order their live
lengths or heights. Marks have their native relative ray presentation at each
anchor. Parent PairMarkHeight supplies this equality on the clean support. -/
def PairAt (N Y l : ℝ) (W : ℝ→ℂ) (bΦ mesh ε Z : ℝ)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀ (T : Finset Slot) (θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr) (w σ₁ σ₂ v₁ v₂ : Slot→ℝ)
    (t₁ t₂ height : ℝ),
    (∀ i,0 ≤ w i) → (∀ i,w i ≤  mesh) →
    (∀ i,(33/50:ℝ) ≤ σ₁ i) → (∀ i,σ₁ i ≤ (33/50:ℝ)) →
    (∀ i,(33/50:ℝ) ≤ σ₂ i) → (∀ i,σ₂ i ≤ (33/50:ℝ)) →
    0 ≤ height → (∀ i,|v₁ i| ≤ height) → (∀ i,|v₂ i| ≤ height) → (∑ i∈T,w i) ≤ l →
  ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
    length Z X₁ ≤ N → length Z X₂ ≤ Y →
  ∀ (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ),
    (∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
    (∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
    (∀ u∈s,rowNorm u ≤ Z) →
    (∀ u∈s,∀ i∈T,‖mark i u‖=
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀₁ θ₁ W Z w σ₁ v₁ i) t₁ (Z^(w i))‖) →
    (∀ u∈s,∀ i∈T,‖mark i u‖=
      ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀₂ θ₂ W Z w σ₂ v₂ i) t₂ (Z^(w i))‖) →
    finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark  ≤ 
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*Z^(1+ε)

/-- Early mesh; then finite slot family, ray dictionary and fixed data; then
one finite control set and degree before every live profile, height or row. -/
def PairUnitBox (N Y l mesh ε : ℝ) : Prop :=
  ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
  ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM  ≤  Hr),
  ∀ W : ℝ→ℂ, ContDiff ℝ ∞ W → Function.support W⊆Set.Icc (1:ℝ) 2 →
  ∀ bΦ : ℝ, 2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
  ∀ (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O),
    Q₁ ≤ rayM → internalQ Q₁ η₀₁ ≠ 0 → internalQ Q₁ η₀₁ ≠ ⊤ →
    internalQ Q₁ η₀₁ ≤ Ideal.span {(72:O)} →
    Q₂ ≤ rayM → internalQ Q₂ η₀₂ ≠ 0 → internalQ Q₂ η₀₂ ≠ ⊤ →
    internalQ Q₂ η₀₂ ≤ Ideal.span {(72:O)} →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop,
        PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z
          η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls C

def PairUniformBox (N Y l : ℝ) : Prop :=
  ∀ ε : ℝ,0 < ε → ∃ mesh : ℝ,0 < mesh ∧ PairUnitBox N Y l mesh ε

def PairOpenWidth (N Y : ℝ) : Prop :=
  ∀ l : ℝ,0 ≤ l → l < sourceWidth N Y → PairUniformBox N Y l

/-- Shrinking only the early mesh does not modify any arithmetic datum. -/
theorem labelled_mesh_mono {α : Type} [Fintype α] [DecidableEq α]
    {N Y l bΦ mesh mesh' ε Z C : ℝ} {W : ℝ→ℂ}
    {η η₀ : Character} {Q : Ideal O} {d : ℕ} {S : Finset (ℕ×ℕ)}
    (hm : mesh ≤ mesh')
    (hsrc : LabelledAt (α:=α) rayM Hr hHr N Y l W 2 (1/4) (9/4) bΦ mesh'
      (33/50) (33/50) 1 1 ε Z η η₀ Q d S C) :
    LabelledAt (α:=α) rayM Hr hHr N Y l W 2 (1/4) (9/4) bΦ mesh
      (33/50) (33/50) 1 1 ε Z η η₀ Q d S C := by
  intro T θ w σ v t height hw hwm
  exact hsrc T θ w σ v t height hw (fun i=>(hwm i).trans hm)

/-- The native strip is PROVED for independent authentic ordinary anchors.
Two native fourths share a strict whole-slot split of the actual marks. -/
theorem native_pair_box (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y l : ℝ} (hy : sourceY ≤ y) (hy' : y ≤ sourceY/(H:ℝ))
    (hn : y ≤ n) (hr : n ≤ sourceRatio*y) (hl0 : 0 ≤ l) (hl : l < sourceWidth n y) :
    PairUniformBox n y l := by
  obtain ⟨q₁,q₂,ms,hms,hq₁,hcap₁,hmean₁,hq₂,hcap₂,hmean₂,hnhi,hyhi,hbudget⟩ :=
    native_split_quotas hy hy' hn hr hl0 hl
  have hbox₁ := QRH.Cycle092.LowActual.native_mean_box hβ hnhi hnhi hq₁ hcap₁ (by linarith : q₁ < (1-n-n)/2)
  have hbox₂ := QRH.Cycle092.LowActual.native_mean_box hβ hyhi hyhi hq₂ hcap₂ (by linarith : q₂ < (1-y-y)/2)
  intro ε hε
  obtain ⟨m₁,hm₁,hsource₁⟩ := hbox₁ ε hε
  obtain ⟨m₂,hm₂,hsource₂⟩ := hbox₂ ε hε
  let mesh := min ms (min m₁ m₂)
  have hm : 0 < mesh := lt_min hms (lt_min hm₁ hm₂)
  have hms' : mesh ≤ ms := min_le_left _ _
  have hm₁' : mesh ≤ m₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hm₂' : mesh ≤ m₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨d₁,S₁,C₁,hC₁,hs₁⟩ := hsource₁ (Fin 2×Slot) rayM Hr hHr W hW hWs bΦ hbΦ
    η₁ η₀₁ Q₁ hQ₁ray hQ₁0 hQ₁top hQ₁72
  obtain ⟨d₂,S₂,C₂,hC₂,hs₂⟩ := hsource₂ (Fin 2×Slot) rayM Hr hHr W hW hWs bΦ hbΦ
    η₂ η₀₂ Q₂ hQ₂ray hQ₂0 hQ₂top hQ₂72
  refine ⟨max d₁ d₂,S₁∪S₂,C₁+C₂+1,by positivity,?_⟩
  filter_upwards [hs₁,hs₂,eventually_gt_atTop (1:ℝ)] with Z hs₁ hs₂ hZ
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi
    hh hv₁ hv₂ hsum p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hmark₁ hmark₂
  obtain ⟨F,hFT,hF,hrest⟩ := partition_selected T w hms.le hq₁ hq₂ hw (fun i=>(hwm i).trans hms') hsum hbudget
  exact native_pair_at rayM Hr hHr (labelled_mesh_mono rayM Hr hHr hm₁' hs₁)
    (labelled_mesh_mono rayM Hr hHr hm₂' hs₂) hC₁.le hC₂.le T F hFT θ₁ θ₂ w σ₁ σ₂ v₁ v₂
    t₁ t₂ height hw hwm hσ₁lo hσ₁hi hσ₂lo hσ₂hi hh hv₁ hv₂ hΦs p X₁ X₂ hX₁ hX₂
    hZ hXN hXY hF hrest s mark hk₁ hk₂ hy (fun u hu i hi=>hmark₁ u hu i (hFT hi))
    (fun u hu i hi=>hmark₂ u hu i (Finset.mem_sdiff.mp hi).1)

#print axioms native_pair_box
end
end QRH.Cycle092.StrongPair
