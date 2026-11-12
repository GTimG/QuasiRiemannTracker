/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Interface.Contract

/-!
# Inverse.Predicate

Facts about the contract `InverseRectAt` (Interface/Contract.lean):

* `ScaleInvariant` slot classes (the class sees the widths only through the scales `Z^(ell i)`);
  `canonicalSlots`, `canonicalSlotsRay`, `anySlots` and the canonical families are scale
  invariant.
* The rescaling `Z ↦ Z^H`: `InverseRectAt` at scale `Z^H` and radius `1` is
  the same statement as `InverseRectAt` at scale `Z` and radius `H`, with mesh and loss
  multiplied by `H` (`inverseRectAt_rescale`, `inverseRectAt_unscale`). Admission is relative to
  the radius, so the rectangle `ρ` does not change: the absolute widths are divided by `H`.
* `InverseRectSourceRadius fam ρ Mlo Mhi mesh ε`: the source at radii `M ∈ [Mlo,Mhi]`;
  `InverseRectSource.rescale`: radius `1` at every scale gives radius `H` at every scale.
* Monotonicity in the loss, the constant, and the radius range.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-! ## Scale-invariant slot classes -/

/-- A slot class that depends on the widths and the scale only through `Z^(ell i)`. -/
def ScaleInvariant (cls : SlotClass) : Prop :=
  ∀ (ι : Type) (data : RowData) (L : ι → Finset (Ideal O)) (ell ell' : ι → ℝ)
    (β : ι → Ideal O → ℂ) (Z Z' hv : ℝ), (∀ i, Z^(ell i) = Z'^(ell' i)) →
    cls ι data L ell β Z hv → cls ι data L ell' β Z' hv

def FamilyScaleInvariant (fam : SlotClass → Prop) : Prop :=
  ∀ cls, fam cls → ScaleInvariant cls

theorem anySlots_scaleInvariant : ScaleInvariant anySlots :=
  fun _ _ _ _ _ _ _ _ _ _ _ => trivial

theorem canonicalSlots_scaleInvariant (W : ℝ → ℂ) (σ : ℝ) :
    ScaleInvariant (canonicalSlots W σ) := by
  intro ι data L ell ell' β Z Z' hv hs hc
  obtain ⟨rayM,hne,H,hH,θ,v,hvb,h⟩ := hc
  refine ⟨rayM,hne,H,hH,θ,v,hvb,fun i => ?_⟩
  rw [← hs i]
  exact h i

theorem canonicalSlotsRay_scaleInvariant (W : ℝ → ℂ) (σ : ℝ) (rayM : Ideal O) [NeZero rayM]
    (G : SlotTwist rayM) (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) :
    ScaleInvariant (canonicalSlotsRay W σ rayM G hH) := by
  intro ι data L ell ell' β Z Z' hv hs hc
  obtain ⟨θ,v,hvb,h⟩ := hc
  refine ⟨θ,v,hvb,fun i => ?_⟩
  rw [← hs i]
  exact h i

/-- `canonicalFamily` (the fixed-ray family) is scale invariant. -/
theorem canonicalFamily_scaleInvariant : FamilyScaleInvariant canonicalFamily := by
  rintro cls ⟨W,_,_,rayM,_,G,hH,rfl⟩
  exact canonicalSlotsRay_scaleInvariant W _ rayM G hH

theorem canonicalFamilyFree_scaleInvariant : FamilyScaleInvariant canonicalFamilyFree := by
  rintro cls ⟨W,_,_,rfl⟩
  exact canonicalSlots_scaleInvariant W _

theorem allFamily_scaleInvariant_of (h : ∀ cls, ScaleInvariant cls) :
    FamilyScaleInvariant allFamily := fun cls _ => h cls

/-! ## The sum under rescaling -/

theorem inverseMarkedSum_congr_scale (data : RowData) (Φ : ℝ → ℂ) {ι : Type} [Fintype ι]
    (L : ι → Finset (Ideal O)) (ell ell' : ι → ℝ) (β : ι → Ideal O → ℂ)
    (rows : Finset HeckeInverseAmplification.NonzeroElement) (Z Z' r r' θ : ℝ)
    (hr : Z^r = Z'^r') (hs : ∀ i, Z^(ell i) = Z'^(ell' i)) :
    inverseMarkedSum data Φ L ell β rows Z r θ = inverseMarkedSum data Φ L ell' β rows Z' r' θ := by
  unfold inverseMarkedSum
  simp only [hr, hs]

theorem rpow_div_rescale {Z H x : ℝ} (hZ : 0 ≤ Z) (hH : H ≠ 0) :
    (Z^H)^(x/H) = Z^x := by
  rw [← Real.rpow_mul hZ]
  congr 1
  field_simp

theorem rpow_mul_rescale {Z H x : ℝ} (hZ : 0 ≤ Z) :
    (Z^H)^x = Z^(H*x) := by
  rw [← Real.rpow_mul hZ]

/-! ## Rescaling -/

/-- Radius `1` at scale `Z^H` gives radius `H` at scale `Z` (mesh and loss times `H`). -/
theorem inverseRectAt_rescale {cls : SlotClass} (hcls : ScaleInvariant cls) {ρ : AnchorRect}
    (Φ : ℝ → ℂ) (K : ℕ) (mesh ε Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H)
    (data : RowData) (degree : ℕ) (C : ℝ)
    (h : InverseRectAt cls ρ Φ K mesh 1 1 ε (Z^H) data degree C) :
    InverseRectAt cls ρ Φ K (H*mesh) H H (H*ε) Z data degree C := by
  intro ι _ _ hK L ell β hv hv0 hc hell hmesh hp hratio hβ hlarge M hM1 hM2 r hadm rows hrows θ
  have hM : M = H := le_antisymm hM2 hM1
  subst hM
  have hsc (i : ι) : Z^(ell i) = (Z^M)^(ell i / M) := (rpow_div_rescale hZ.le hH.ne').symm
  have hsc' (i : ι) : (Z^M)^(ell i / M) = Z^(ell i) := rpow_div_rescale hZ.le hH.ne'
  have hc' := hcls ι data L ell (fun i => ell i / M) β Z (Z^M) hv hsc hc
  have hsum : (∑ i, ell i / M) = (∑ i, ell i) / M := by rw [Finset.sum_div]
  obtain ⟨hr0,hrP,hS0,hSS⟩ := hadm
  have hadm' : ρ.Admissible (r/M) (∑ i, ell i / M) 1 := by
    rw [hsum]
    refine ⟨div_nonneg hr0 hH.le, ?_, div_nonneg hS0 hH.le, ?_⟩
    · rw [div_le_iff₀ hH]; linarith
    · rw [div_le_iff₀ hH]; linarith
  have hb := h hK L (fun i => ell i / M) β hv hv0 hc' (fun i => div_nonneg (hell i) hH.le)
    (fun i => by rw [div_le_iff₀ hH]; linarith [hmesh i]) hp
    (fun i P hP => by rw [hsc' i]; exact hratio i P hP) hβ
    (fun i => by rw [hsc' i]; exact hlarge i) 1 le_rfl le_rfl (r/M) hadm' rows
    (fun u hu => by rw [Real.rpow_one]; exact hrows u hu) θ
  rw [inverseMarkedSum_congr_scale data Φ L ell (fun i => ell i / M) β rows Z (Z^M) r (r/M) θ
    (rpow_div_rescale hZ.le hH.ne').symm hsc]
  refine hb.trans (le_of_eq ?_)
  rw [rpow_mul_rescale hZ.le, show M*(1+ε) = M+M*ε by ring]

/-- Radius `H` at scale `Z` gives radius `1` at scale `Z^H`. -/
theorem inverseRectAt_unscale {cls : SlotClass} (hcls : ScaleInvariant cls) {ρ : AnchorRect}
    (Φ : ℝ → ℂ) (K : ℕ) (mesh ε Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H)
    (data : RowData) (degree : ℕ) (C : ℝ)
    (h : InverseRectAt cls ρ Φ K (H*mesh) H H (H*ε) Z data degree C) :
    InverseRectAt cls ρ Φ K mesh 1 1 ε (Z^H) data degree C := by
  intro ι _ _ hK L ell β hv hv0 hc hell hmesh hp hratio hβ hlarge M hM1 hM2 r hadm rows hrows θ
  have hM : M = 1 := le_antisymm hM2 hM1
  subst hM
  have hsc (i : ι) : (Z^H)^(ell i) = Z^(H*ell i) := rpow_mul_rescale hZ.le
  have hc' := hcls ι data L ell (fun i => H*ell i) β (Z^H) Z hv hsc hc
  have hsum : (∑ i, H*ell i) = H*(∑ i, ell i) := by rw [Finset.mul_sum]
  obtain ⟨hr0,hrP,hS0,hSS⟩ := hadm
  have hadm' : ρ.Admissible (H*r) (∑ i, H*ell i) H := by
    rw [hsum]
    refine ⟨mul_nonneg hH.le hr0, ?_, mul_nonneg hH.le hS0, ?_⟩
    · have := mul_le_mul_of_nonneg_left hrP hH.le; linarith
    · have := mul_le_mul_of_nonneg_left hSS hH.le; linarith
  have hb := h hK L (fun i => H*ell i) β hv hv0 hc' (fun i => mul_nonneg hH.le (hell i))
    (fun i => mul_le_mul_of_nonneg_left (hmesh i) hH.le) hp
    (fun i P hP => by rw [← hsc i]; exact hratio i P hP) hβ
    (fun i => by rw [← hsc i]; exact hlarge i) H le_rfl le_rfl (H*r) hadm' rows
    (fun u hu => by have h1 := hrows u hu; rwa [Real.rpow_one] at h1) θ
  rw [inverseMarkedSum_congr_scale data Φ L ell (fun i => H*ell i) β rows (Z^H) Z r (H*r) θ
    (rpow_mul_rescale hZ.le) hsc]
  refine hb.trans (le_of_eq ?_)
  rw [rpow_mul_rescale hZ.le, show H*(1+ε) = H+H*ε by ring]

/-! ## Monotonicity -/

theorem inverseRectAt_mono {cls : SlotClass} {ρ : AnchorRect} (Φ : ℝ → ℂ) (K : ℕ)
    (mesh Mmin Mmax ε ε' Z : ℝ) (data : RowData) (degree : ℕ) (C C' : ℝ)
    (Mmin' Mmax' : ℝ) (hMmin : Mmin ≤ Mmin') (hMmax : Mmax' ≤ Mmax)
    (hZ : 1 ≤ Z) (hε : ε ≤ ε') (hC0 : 0 ≤ C) (hC : C ≤ C')
    (hs : InverseRectAt cls ρ Φ K mesh Mmin Mmax ε Z data degree C) :
    InverseRectAt cls ρ Φ K mesh Mmin' Mmax' ε' Z data degree C' := by
  intro ι _ _ hK L ell β hv hv0 hc h1 h2 h3 h4 h5 h6 M hMlo hMhi r hadm rows hrows θ
  refine (hs hK L ell β hv hv0 hc h1 h2 h3 h4 h5 h6 M (hMmin.trans hMlo) (hMhi.trans hMmax) r hadm
    rows hrows θ).trans ?_
  have hpos : 0 ≤ ((1+‖θ‖+hv)^degree)^2 := by positivity
  have hZM : Z^(M+ε) ≤ Z^(M+ε') := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hZ0 : 0 ≤ Z^(M+ε) := Real.rpow_nonneg (zero_le_one.trans hZ) _
  apply mul_le_mul_of_nonneg_right _ hpos
  exact mul_le_mul hC hZM hZ0 (hC0.trans hC)

/-! ## Sources at a fixed radius range -/

/-- The inverse contract at radii `M ∈ [Mlo,Mhi]` (same quantifier order as `InverseRectSource`,
which is the case `Mlo = Mhi = 1`). -/
def InverseRectSourceRadius (fam : SlotClass → Prop) (ρ : AnchorRect) (Mlo Mhi mesh ε : ℝ) :
    Prop :=
  ∀ K : ℕ, ∀ cls : SlotClass, fam cls →
  ∀ (Φ : ℝ → ℂ) (ao bo : ℝ), 0 < ao → ao ≤ bo → Function.support Φ ⊆ Icc ao bo →
    ContDiff ℝ ∞ Φ →
  ∀ data : RowData, ∃ (degree : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → InverseRectAt cls ρ Φ K mesh Mlo Mhi ε Z data degree C

theorem inverseRectSourceRadius_one {fam : SlotClass → Prop} {ρ : AnchorRect} {mesh ε : ℝ} :
    InverseRectSourceRadius fam ρ 1 1 mesh ε ↔ InverseRectSource fam ρ mesh ε := Iff.rfl

/-- Rescaling at the source level: the radius-one source at every scale is a radius-`H` source. -/
theorem InverseRectSource.rescale {fam : SlotClass → Prop} (hfam : FamilyScaleInvariant fam)
    {ρ : AnchorRect} {mesh ε H : ℝ} (hH : 0 < H) (hs : InverseRectSource fam ρ mesh ε) :
    InverseRectSourceRadius fam ρ H H (H*mesh) (H*ε) := by
  intro K cls hcls Φ ao bo hao hab hΦs hΦ data
  obtain ⟨degree,C,Z₀,hC,hZ₀,hb⟩ := hs K cls hcls Φ ao bo hao hab hΦs hΦ data
  refine ⟨degree,C,Z₀^(1/H),hC,Real.one_lt_rpow hZ₀ (by positivity),fun Z hZ => ?_⟩
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.rpow_pos_of_pos (zero_lt_one.trans hZ₀) _) hZ
  have hZH : Z₀ ≤ Z^H := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans hZ₀.le) _) hZ hH.le
    rwa [← Real.rpow_mul (zero_le_one.trans hZ₀.le), one_div_mul_cancel hH.ne',
      Real.rpow_one] at h1
  have hb' := @hb (Z^H) hZH
  exact @inverseRectAt_rescale cls (hfam cls hcls) ρ Φ K mesh ε Z H hZpos hH data degree C hb'

/-- Converse: a radius-`H` source is a radius-one source. -/
theorem InverseRectSourceRadius.unscale {fam : SlotClass → Prop}
    (hfam : FamilyScaleInvariant fam) {ρ : AnchorRect} {mesh ε H : ℝ} (hH : 0 < H)
    (hs : InverseRectSourceRadius fam ρ H H (H*mesh) (H*ε)) :
    InverseRectSource fam ρ mesh ε := by
  intro K cls hcls Φ ao bo hao hab hΦs hΦ data
  obtain ⟨degree,C,Z₀,hC,hZ₀,hb⟩ := hs K cls hcls Φ ao bo hao hab hΦs hΦ data
  refine ⟨degree,C,Z₀^H,hC,Real.one_lt_rpow hZ₀ hH,fun Z hZ => ?_⟩
  have hZ0 : 0 ≤ Z₀ := zero_le_one.trans hZ₀.le
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.rpow_pos_of_pos (zero_lt_one.trans hZ₀) _) hZ
  have hZ' : Z₀ ≤ Z^(1/H) := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hZ0 _) hZ (by positivity : (0:ℝ) ≤ 1/H)
    rwa [← Real.rpow_mul hZ0, mul_one_div_cancel hH.ne', Real.rpow_one] at h1
  have hZeq : (Z^(1/H))^H = Z := by
    rw [← Real.rpow_mul hZpos.le, one_div_mul_cancel hH.ne', Real.rpow_one]
  have hb' := @hb (Z^(1/H)) hZ'
  have hres := @inverseRectAt_unscale cls (hfam cls hcls) ρ Φ K mesh ε (Z^(1/H)) H
    (Real.rpow_pos_of_pos hZpos _) hH data degree C hb'
  rw [hZeq] at hres
  exact @hres

/-- The uniform child source after rescaling: for every loss `ε` there is a mesh such that the
radius-`H` source holds at loss `ε`. -/
theorem UniformInverseRectSource.rescale {fam : SlotClass → Prop}
    (hfam : FamilyScaleInvariant fam) {ρ : AnchorRect} {H : ℝ} (hH : 0 < H)
    (hs : UniformInverseRectSource fam ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧ InverseRectSourceRadius fam ρ H H mesh ε := by
  intro ε hε
  obtain ⟨mesh,hmesh,hsrc⟩ := hs (ε/H) (div_pos hε hH)
  refine ⟨H*mesh,mul_pos hH hmesh,?_⟩
  have hres := InverseRectSource.rescale hfam hH hsrc
  rwa [mul_div_cancel₀ ε hH.ne'] at hres

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.inverseRectAt_rescale
#print axioms Qrh.MarkedAnchor.Inverse.inverseRectAt_unscale
#print axioms Qrh.MarkedAnchor.Inverse.InverseRectSource.rescale
#print axioms Qrh.MarkedAnchor.Inverse.InverseRectSourceRadius.unscale
#print axioms Qrh.MarkedAnchor.Inverse.UniformInverseRectSource.rescale
