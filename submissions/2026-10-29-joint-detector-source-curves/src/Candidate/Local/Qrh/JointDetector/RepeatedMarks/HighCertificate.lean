/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Ledger
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Rate
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false

/-- The two literal short inverse/plain balances used by the exact checker. -/
def momentDen (ν α β : ℝ) : ℝ := α*β+(5/6-ν)*(α+β)
def momentSave (ν α β inverseConstant plainConstant : ℝ) : ℝ :=
 (5/6)*α*β+(5/6-ν)*(β*inverseConstant+α*plainConstant)

theorem crossingRate_eq_moment {ν p A Z : ℝ} (hν : ν ≠ 0)
 (hJ : crossingDen ν p A ≠ 0) :
 crossingRate ν p A Z =
 1-momentSave ν (ν*(1-p)) (ν*A) (ν*p) (ν*Z)/
   momentDen ν (ν*(1-p)) (ν*A) := by
 have hden : momentDen ν (ν*(1-p)) (ν*A) = ν*crossingDen ν p A := by
   unfold momentDen crossingDen
   ring
 rw [hden]
 unfold crossingRate momentSave
 field_simp [hν,hJ]
 unfold crossingDen
 ring

/-- Polynomial-rational coordinates for a fixed ray v=r*nu*z.
These are exactly the two denominators/saving numerators checked by the
finite source certificates, with no extra power of the density. -/
def rayCapDen (ν r z : ℝ) : ℝ := crossingDen ν (r*z/2) 2
def rayCapSave (c ν r z : ℝ) : ℝ :=
 ν*rayCapDen ν r z-(5/6-ν)*ν*(1-r*z/2)*(1-r*z*c)
def rayBudgetDen (L ν r z : ℝ) : ℝ :=
 crossingDen ν (r*z/2) (2-2*r*z/L)
def rayBudgetSave (B L ν r z : ℝ) : ℝ :=
 ν*rayBudgetDen L ν r z-(5/6-ν)*ν*(1-r*z/2)*(1-r*z*B/L)

theorem capCrossingRate_eq_ray {c ν r z : ℝ} (hD : rayCapDen ν r z ≠ 0) :
 capCrossingRate c ν (r*z/2) = 1-rayCapSave c ν r z/rayCapDen ν r z := by
 unfold capCrossingRate crossingRate rayCapSave rayCapDen at *
 field_simp
 <;> ring

private theorem rational_saving_identity (ν V D : ℝ) (hD : D ≠ 0) :
 1-ν+V/D=1-(ν*D-V)/D := by
 field_simp
 <;> ring

theorem budgetCrossingRate_eq_ray {B L ν r z : ℝ}
 (hD : rayBudgetDen L ν r z ≠ 0) :
 budgetCrossingRate B L ν (r*z/2) =
   1-rayBudgetSave B L ν r z/rayBudgetDen L ν r z := by
 have hA : 2-4*(r*z/2)/L=2-2*r*z/L := by ring
 have hZ : 2*(r*z/2)*B/L=r*z*B/L := by ring
 unfold budgetCrossingRate
 rw [hA,hZ]
 unfold crossingRate rayBudgetSave rayBudgetDen
 exact rational_saving_identity _ _ _ hD

theorem rawRepeatedCountRate_eq_ray {B L c ν r z : ℝ} (hν : ν ≠ 0)
 (hcap : rayCapDen ν r z ≠ 0) (hbudget : rayBudgetDen L ν r z ≠ 0) :
 rawRepeatedCountRate B L c ν (r*ν*z) =
 max (max (1-rayCapSave c ν r z/rayCapDen ν r z)
   (1-rayBudgetSave B L ν r z/rayBudgetDen L ν r z)) (1-ν*B) := by
 have he : r*ν*z/(2*ν)=r*z/2 := by field_simp
 unfold rawRepeatedCountRate
 rw [he,capCrossingRate_eq_ray hcap,budgetCrossingRate_eq_ray hbudget]

/-- Rational branch in the full physical weighted amplitude, before the
supremum is taken. Here K/D is the count saving, not the count itself. -/
def weightedRatio (K D : ℝ → ℝ) (H S z : ℝ) : ℝ :=
  (1-K z/D z)*H+z*S

theorem weightedRatio_hasDerivAt {K D : ℝ → ℝ} {K' D' H S z : ℝ}
 (hK : HasDerivAt K K' z) (hD : HasDerivAt D D' z) (hD0 : D z ≠ 0) :
 HasDerivAt (weightedRatio K D H S)
   (((K z*D'-K'*D z)*H+S*(D z)^2)/(D z)^2) z := by
 have hh := (((hasDerivAt_const z (1:ℝ)).sub (hK.div hD hD0)).mul_const H).add
   ((hasDerivAt_id z).mul_const S)
 convert hh using 1
 · funext t
   rfl
 · field_simp
   <;> ring

theorem weightedRatio_monotoneOn {K D : ℝ → ℝ} {K' D' : ℝ → ℝ} {H S lo hi : ℝ}
 (hK : ∀ z ∈ Set.Icc lo hi, HasDerivAt K (K' z) z)
 (hD : ∀ z ∈ Set.Icc lo hi, HasDerivAt D (D' z) z)
 (hD0 : ∀ z ∈ Set.Icc lo hi, 0 < D z)
 (hnum : ∀ z ∈ Set.Icc lo hi,
   0 ≤ (K z*D' z-K' z*D z)*H+S*(D z)^2) :
 MonotoneOn (weightedRatio K D H S) (Set.Icc lo hi) := by
 have hh z hz := weightedRatio_hasDerivAt (H:=H) (S:=S) (hK z hz) (hD z hz) (hD0 z hz).ne'
 apply monotoneOn_of_deriv_nonneg (convex_Icc lo hi)
 · intro z hz
   exact (hh z hz).continuousAt.continuousWithinAt
 · intro z hz
   exact (hh z (interior_subset hz)).differentiableAt.differentiableWithinAt
 · intro z hz
   rw [(hh z (interior_subset hz)).deriv]
   exact div_nonneg (hnum z (interior_subset hz)) (sq_nonneg _)

/-- A per-width derivative reserve remains valid at every retained physical
width S/H above its crossing value. The height is paid only once. -/
theorem derivative_reserve_transport {a s H S D K Dz Kz : ℝ}
 (ha : 0 ≤ a) (hH : 0 ≤ H) (hS : s*H ≤ S)
 (hbase : 0 ≤ K*Dz-Kz*D+a*s*D^2) :
 0 ≤ (K*Dz-Kz*D)*H+a*S*D^2 := by
 have h₁ := mul_nonneg hH hbase
 have h₂ := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hS)) (sq_nonneg D)
 nlinarith

/-- Exact selected-count finite difference; no density-dependent contour or
termwise continuation is involved. -/
theorem detectorRate_difference {ν a b : ℝ}
 (ha : a ≤ ν) (hb : b ≤ ν) (hν : ν ≤ 3/4) :
 detectorRate ν a-detectorRate ν b =
   3*(1-ν)^2*(b-a)/((3-ν-2*a)*(3-ν-2*b)) := by
 simpa only [detectorRate,if_pos ha,if_pos hb] using
   count_delta_difference ha hb hν

theorem selectedWeighted_antitone {ν lo H S : ℝ}
 (hν : ν ≤ 3/4) (hlo : (1/2:ℝ) ≤ lo)
 (hH : 0 ≤ H) (hS : S ≤ H/10) :
 AntitoneOn (fun v => detectorRate ν v*H+v*S) (Set.Icc lo ν) := by
 intro a ha b hb hab
 have hνlo : (1/2:ℝ) ≤ ν := hlo.trans (ha.1.trans ha.2)
 have hDa : 0 < 3-ν-2*a := by linarith [ha.2]
 have hDb : 0 < 3-ν-2*b := by linarith [hb.2]
 have hDahi : 3-ν-2*a ≤ 5*(1-ν) := by linarith [ha.1]
 have hDbhi : 3-ν-2*b ≤ 5*(1-ν) := by linarith [hb.1]
 have hnu1 : 0 ≤ 5*(1-ν) := by linarith
 have hprod : (3-ν-2*a)*(3-ν-2*b) ≤ 25*(1-ν)^2 := by
   have hh := mul_le_mul hDahi hDbhi hDb.le hnu1
   nlinarith only [hh]
 have hDp : 0 < (3-ν-2*a)*(3-ν-2*b) := mul_pos hDa hDb
 have hquot : (3/25:ℝ) ≤ 3*(1-ν)^2/((3-ν-2*a)*(3-ν-2*b)) := by
   apply (le_div_iff₀ hDp).mpr
   nlinarith only [hprod]
 have hdiff := mul_le_mul_of_nonneg_right hquot (sub_nonneg.mpr hab)
 have hrate : (3/25:ℝ)*(b-a) ≤ detectorRate ν a-detectorRate ν b := by
   rw [detectorRate_difference ha.2 hb.2 hν]
   convert hdiff using 1 <;> ring
 have hmul := mul_le_mul_of_nonneg_right hrate hH
 have hslot := mul_le_mul_of_nonneg_right hS (sub_nonneg.mpr hab)
 nlinarith only [hmul,hslot,mul_nonneg hH (sub_nonneg.mpr hab)]

/-- The scalar checker certifies this cleared numerator. Positive denominator
transport recovers the literal HIGH reserve with every physical term. -/
theorem high_reserve_of_cleared {D K ν P H a S u reserve : ℝ} (hD : 0 < D)
 (hnum : reserve*D ≤ H*K-ν*P*D-a*S*D+u*D) :
 reserve ≤ u-(ν*P+(1-K/D-1)*H+a*S) := by
 have he : u-(ν*P+(1-K/D-1)*H+a*S) =
   (H*K-ν*P*D-a*S*D+u*D)/D := by
   field_simp
   <;> ring
 rw [he]
 exact (le_div_iff₀ hD).mpr hnum

/-- Splitting the amplitude interval is legitimate only before taking its
supremum. Both sides here bound the same weighted count function. -/
theorem weighted_split_bound {f lower upper : ℝ → ℝ} {cut lo hi bound : ℝ}
 (hcut : cut ∈ Set.Icc lo hi)
 (hl : ∀ z ∈ Set.Icc lo cut, f z ≤ lower z)
 (hu : ∀ z ∈ Set.Icc cut hi, f z ≤ upper z)
 (hmono : MonotoneOn lower (Set.Icc lo cut))
 (hanti : AntitoneOn upper (Set.Icc cut hi))
 (hlc : lower cut ≤ bound) (huc : upper cut ≤ bound) :
 ∀ z ∈ Set.Icc lo hi, f z ≤ bound := by
 intro z hz
 rcases le_total z cut with h | h
 · exact (hl z ⟨hz.1,h⟩).trans ((hmono ⟨hz.1,h⟩ ⟨hcut.1,le_rfl⟩ h).trans hlc)
 · exact (hu z ⟨h,hz.2⟩).trans ((hanti ⟨le_rfl,hcut.2⟩ ⟨h,hz.2⟩ h).trans huc)
theorem weighted_max_identity (a b P H S : ℝ) (hH : 0 ≤ H) :
 P+(max a b-1)*H+S = max (P+(a-1)*H+S) (P+(b-1)*H+S) := by
 rcases le_total a b with h | h
 · rw [max_eq_right h, max_eq_right]
   nlinarith only [mul_nonneg (sub_nonneg.mpr h) hH]
 · rw [max_eq_left h, max_eq_left]
   nlinarith only [mul_nonneg (sub_nonneg.mpr h) hH]

theorem rawWeighted_monotoneOn {B L c ν P H S a : ℝ} (hH : 0 ≤ H)
 (hcap : MonotoneOn (fun v => ν*P+(capCrossingRate c ν (v/(2*ν))-1)*H+v*S) (Set.Icc 0 a))
 (hbudget : MonotoneOn (fun v => ν*P+(budgetCrossingRate B L ν (v/(2*ν))-1)*H+v*S) (Set.Icc 0 a))
 (htail : MonotoneOn (fun v => ν*P+((1-ν*B)-1)*H+v*S) (Set.Icc 0 a)) :
 MonotoneOn (fun v => ν*P+(rawRepeatedCountRate B L c ν v-1)*H+v*S) (Set.Icc 0 a) := by
 intro x hx y hy hxy
 have hc := hcap hx hy hxy
 have hb := hbudget hx hy hxy
 have ht := htail hx hy hxy
 unfold rawRepeatedCountRate
 dsimp only []
 rw [weighted_max_identity _ _ _ _ _ hH,weighted_max_identity _ _ _ _ _ hH,
   weighted_max_identity _ _ _ _ _ hH,weighted_max_identity _ _ _ _ _ hH]
 exact max_le_max (max_le_max hc hb) ht

theorem selectedTerm_antitone {ν lo P H S : ℝ}
 (hν : ν ≤ 3/4) (hlo : (1/2:ℝ) ≤ lo)
 (hH : 0 ≤ H) (hS : S ≤ H/10) :
 AntitoneOn (fun v => ν*P+(detectorRate ν v-1)*H+v*S) (Set.Icc lo ν) := by
 intro a ha b hb hab
 have hh := selectedWeighted_antitone hν hlo hH hS ha hb hab
 nlinarith only [hh]

theorem combineSelected_le_raw (rate : ℝ → ℝ → ℝ) (ν v : ℝ) :
 combineSelected rate ν v ≤ rate ν v := by
 unfold combineSelected
 split_ifs
 · exact min_le_left _ _
 · exact le_rfl

theorem combineSelected_le_selected (rate : ℝ → ℝ → ℝ) {ν v : ℝ}
 (hv : (500001/1000000:ℝ) ≤ v) :
 combineSelected rate ν v ≤ detectorRate ν v := by
 unfold combineSelected
 rw [if_pos hv]
 exact min_le_right _ _

/-- The actual same-event combined weighted rate is bounded by the raw rate
below the divider and by the selected rate above it. -/
theorem combined_weighted_bound {rate : ℝ → ℝ → ℝ} {ν a P H S bound : ℝ}
 (hν : ν ≤ 3/4) (ha : a ∈ Set.Icc (500001/1000000:ℝ) ν)
 (hH : 0 ≤ H) (hS : S ≤ H/10)
 (hmono : MonotoneOn (fun v => ν*P+(rate ν v-1)*H+v*S) (Set.Icc 0 a))
 (hraw : ν*P+(rate ν a-1)*H+a*S ≤ bound)
 (hselected : ν*P+(detectorRate ν a-1)*H+a*S ≤ bound) :
 ∀ v ∈ Set.Icc (0:ℝ) ν,
 ν*P+(combineSelected rate ν v-1)*H+v*S ≤ bound := by
 apply weighted_split_bound (cut:=a)
   (lower:=fun v => ν*P+(rate ν v-1)*H+v*S)
   (upper:=fun v => ν*P+(detectorRate ν v-1)*H+v*S)
 · exact ⟨by linarith [ha.1],ha.2⟩
 · intro v hv
   have hh := mul_le_mul_of_nonneg_right (combineSelected_le_raw rate ν v) hH
   nlinarith only [hh]
 · intro v hv
   have hh := mul_le_mul_of_nonneg_right
     (combineSelected_le_selected rate (ν:=ν) (ha.1.trans hv.1)) hH
   nlinarith only [hh]
 · exact hmono
 · exact selectedTerm_antitone hν (by linarith [ha.1]) hH hS
 · exact hraw
 · exact hselected


/-- Transfer a proved monotonicity on the fixed unit amplitude interval to
its actual ray interval. The rescaling is fixed within this source stage. -/
theorem scaled_weighted_monotone {f g : ℝ → ℝ} {a C : ℝ} (ha : 0 < a)
 (he : ∀ z ∈ Set.Icc (0:ℝ) 1, f (a*z)=C+g z)
 (hm : MonotoneOn g (Set.Icc (0:ℝ) 1)) :
 MonotoneOn f (Set.Icc (0:ℝ) a) := by
 intro x hx y hy hxy
 have hxx : x/a ∈ Set.Icc (0:ℝ) 1 :=
   ⟨div_nonneg hx.1 ha.le,(div_le_one ha).mpr hx.2⟩
 have hyy : y/a ∈ Set.Icc (0:ℝ) 1 :=
   ⟨div_nonneg hy.1 ha.le,(div_le_one ha).mpr hy.2⟩
 have hh := hm hxx hyy ((div_le_div_iff_of_pos_right ha).mpr hxy)
 have hex := he (x/a) hxx
 have hey := he (y/a) hyy
 have hxx' : a*(x/a)=x := by field_simp
 have hyy' : a*(y/a)=y := by field_simp
 rw [hxx'] at hex
 rw [hyy'] at hey
 linarith only [hh,hex,hey]

/-- Close the literal family reserve from a whole-label weighted bound.
This is an adapter, never an assumed count or operator estimate. -/
theorem familyOfRate_highReserve (q : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) (3/4))
 (rate : ℝ → ℝ → ℝ)
 (hrate : ∀ ν ∈ Set.Icc q (3/4:ℝ), ∀ v ∈ Set.Icc (0:ℝ) ν,
    rate ν v ∈ Set.Icc (0:ℝ) 1)
 (B L W u reserve : ℝ)
 (hbound : ∀ ν ∈ Set.Icc q (3/4:ℝ), ∀ v ∈ Set.Icc (0:ℝ) ν,
   ν*(B-L*W)+(rate ν v-1)*(1-6*u)+v*(W-u) ≤ u-reserve) :
 HighReserve (familyOfRate q hq rate hrate) B L W u reserve := by
 intro i
 have hh := hbound i.val.1 ⟨i.property.1,i.property.2.1⟩ i.val.2 i.property.2.2
 change reserve ≤ u-(i.val.1*(B-L*W)+(rate i.val.1 i.val.2-1)*(1-6*u)+i.val.2*(W-u))
 linarith only [hh]

end
end Qrh.JointDetector.RepeatedMarks
