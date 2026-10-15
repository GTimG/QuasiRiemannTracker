/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorBatch
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstActualFrequencyBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.StageMargins
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.WidthRanges
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountCrossing
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectedTruncation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectionLength
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersHighData

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.Crossing ; sha256 e62904966711721f3a59ecb04bfd36c708f5d0568eb9b1bdda3b2ef74b05bbf4 -/
section


/-! Variable plain-moment coefficient for Cycle25. Adapted from pinned
OpenAI DetectorRowCountCrossing (Apache-2.0); original definitions preserved. -/
namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section

def b (p κ : ℝ) : ℝ := p/(3*κ)
def denominator (p κ : ℝ) : ℝ := 3-p-2*b p κ
def primeWeight (p κ : ℝ) : ℝ := 2*(1-p)*(1-b p κ)
def coefficient (p κ : ℝ) : ℝ := primeWeight p κ/denominator p κ
def crossing (p κ t : ℝ) : ℝ := ((2-2*b p κ)*t-p+b p κ)/denominator p κ
def inverseExponent (δ p r : ℝ) : ℝ := 1-δ*(p+(1-p)*r)
def plainExponent (δ p κ t r : ℝ) : ℝ := 1-δ*(b p κ+(2-2*b p κ)*(t-r))
def shortExponent (δ p κ t : ℝ) : ℝ := 1-δ+δ*coefficient p κ*(3/2-t)
abbrev longExponent := HeckeDetectorRowCount.longExponent

lemma b_bounds {p κ : ℝ} (hp : 0≤ p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    0≤ b p κ ∧ 4*p/9≤ b p κ ∧ b p κ≤10*p/21 ∧ b p κ≤ p := by
  have hd : 0<3*κ := by linarith
  unfold b
  refine ⟨div_nonneg hp hd.le,(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_⟩
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hk1)]
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hk)]
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hk)]

lemma denominator_lower {p κ : ℝ} (hp : 0≤ p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) : 85/42≤ denominator p κ := by
  have hb := b_bounds hp hp1 hk hk1
  unfold denominator
  linarith

theorem crossing_bounds {p κ t : ℝ} (hp : 0≤ p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (ht : 1≤ t) (ht1 : t≤3/2) :
    23/37≤ crossing p κ t ∧ crossing p κ t≤1 ∧
      1/3≤ t-crossing p κ t ∧ t-crossing p κ t≤1/2 := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : 0< denominator p κ := lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1)
  have hpt := mul_le_mul_of_nonneg_left ht (show 0≤2-2*b p κ by linarith)
  have hpt1 := mul_le_mul_of_nonneg_left ht1 (show 0≤2-2*b p κ by linarith)
  have hmt := mul_le_mul_of_nonneg_left ht (show 0≤1-p by linarith)
  have hmt1 := mul_le_mul_of_nonneg_left ht1 (show 0≤1-p by linarith)
  have he : t-crossing p κ t=((1-p)*t+p-b p κ)/denominator p κ := by
    unfold crossing
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hd.ne']
    unfold denominator
    ring
  refine ⟨(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,?_,?_⟩
  · unfold denominator
    nlinarith
  · unfold denominator
    nlinarith
  · rw [he]
    apply (le_div_iff₀ hd).mpr
    unfold denominator
    nlinarith
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    unfold denominator
    nlinarith

lemma inverse_at_crossing (δ p κ t : ℝ) (hd : denominator p κ≠0) :
    inverseExponent δ p (crossing p κ t)=shortExponent δ p κ t := by
  unfold inverseExponent crossing shortExponent coefficient primeWeight
  field_simp
  unfold denominator
  ring
lemma plain_at_crossing (δ p κ t : ℝ) (hd : denominator p κ≠0) :
    plainExponent δ p κ t (crossing p κ t)=shortExponent δ p κ t := by
  unfold plainExponent crossing shortExponent coefficient primeWeight
  field_simp
  unfold denominator
  ring

theorem selected_short_bound {δ p κ t r : ℝ} (hδ : 0≤δ) (hp : 0≤ p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    (r≤ crossing p κ t → plainExponent δ p κ t r≤ shortExponent δ p κ t) ∧
      (crossing p κ t≤ r → inverseExponent δ p r≤ shortExponent δ p κ t) := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : denominator p κ≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1))
  constructor
  · intro hr
    rw [←plain_at_crossing δ p κ t hd]
    unfold plainExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤2-2*b p κ by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hr
    rw [←inverse_at_crossing δ p κ t hd]
    unfold inverseExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤1-p by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]

lemma short_ge_base {δ p κ t : ℝ} (hδ : 0≤δ) (hp : 0≤ p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (ht : t≤3/2) : 1-δ≤ shortExponent δ p κ t := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : 0< denominator p κ := lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1)
  have hw : 0≤ primeWeight p κ := by unfold primeWeight; exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  unfold shortExponent coefficient
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hδ (div_nonneg hw hd.le)) (by linarith))

theorem plain_capacity_comparison {δ p κ t r m γ : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤1) (hp : 0≤ p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (hγ : 0≤γ) (hlength : t-r-γ≤ m) :
    1-2*δ*m-2*(δ*p)*(1-2*m)/(6*κ)≤ plainExponent δ p κ t r+2*γ := by
  have hd : 6*κ≠0 := by linarith
  have hb := b_bounds hp hp1 hk hk1
  have hc : 0≤δ*(2-2*b p κ) := mul_nonneg hδ (by linarith)
  have hc1 : δ*(2-2*b p κ)≤2 := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (show 0≤2-2*b p κ by linarith)
    nlinarith
  have hid : (1-2*δ*m-2*(δ*p)*(1-2*m)/(6*κ))-plainExponent δ p κ t r =
      δ*(2-2*b p κ)*(t-r-m) := by unfold plainExponent b; field_simp; ring
  have hl := mul_le_mul_of_nonneg_left (show t-r-m≤γ by linarith) hc
  have he := mul_le_mul_of_nonneg_right hc1 hγ
  linarith

end
end OAI.SevenEighths.Cycle25DetectorRowCount
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.Crossing -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.Moments ; sha256 f4b63486416cf74c845e12a87ef145c550dba8c0dcd0b199cfacb52ba91ff113 -/
section


/-! Cycle25 moment contract. The analytic moments are actual physical row sums,
with the original dictionary; κplain is separate from inverse amplification. -/
namespace OAI.SevenEighths.Cycle25DetectorRawFiber
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open HeckeDetectorCoefficientTransfer
open Set HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles HeckeDetectorPlainFiberCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

structure Moments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (κplain c κinverse C height εm : ℝ) : Prop where
  original : HeckeDetectorRawFiber.Moments F 0 c κinverse C height εm
  plain_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    2*F.m+6*κplain*(∑ s∈selected,F.widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2≤ C*U^(1+εm)

theorem plain_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {κplain c κinverse C height εm : ℝ} (moments : Moments F κplain c κinverse C height εm)
    (hU : 1< U) (ha : 1/2≤ a) (hκ : 0≤κplain) (hC : 0≤ C) (hh : 0≤ height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (z : ℝ) (hz : 0≤ z) (hz' : z≤7/37) (hcap : 2*F.m+6*κplain*z≤1) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm) := by
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z κplain εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin hκ hC hh hf hcap moments.plain_marked

structure BaseMoments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
    let W := twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t
    RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  inverse_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    F.r+2*(∑ s∈selected,F.widths s)<1 → 2*F.r+8*(∑ s∈selected,F.widths s)<3 →
    ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*F.physicalProduct selected u‖^2≤ C*U^(1+εm)
  plain_unmarked : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2≤
          C*U^(max 1 (2*F.m)+εm)

def MarkedPlainMoment (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (κplain C height εm : ℝ) : Prop := ∀ selected : Finset Slot,selected⊆F.slots →
    2*F.m+6*κplain*(∑ s∈selected,F.widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2≤ C*U^(1+εm)


theorem Moments.of_fields (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {κplain c κinverse C height εm : ℝ} (hk : κplain≤3/4)
    (base : BaseMoments F c κinverse C height εm)
    (plain : MarkedPlainMoment F κplain C height εm) :
    Moments F κplain c κinverse C height εm := by
  refine ⟨⟨base.inverse_raw,base.inverse_marked,?_,base.plain_unmarked⟩,plain⟩
  intro selected hselected hcap
  apply plain selected hselected
  have hs : 0≤∑s∈selected,F.widths s := Finset.sum_nonneg (fun s hs=>(F.widths_pos s (hselected hs)).le)
  have hh := mul_le_mul_of_nonneg_right hk hs
  norm_num at hcap
  nlinarith
end
end OAI.SevenEighths.Cycle25DetectorRawFiber
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.Moments -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.SlotWidths ; sha256 06834a05c1ff19356870c584ff732efbd3201d82e20ba95a29218f2b00df3d86 -/
section

namespace OAI.SevenEighths.Cycle25WeightedHighRowFamily
noncomputable section
open scoped BigOperators
lemma physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin dmax mesh : ℝ)
    (hdmin : 0< dmin) (hd : dmin≤ d) (hdmax : d≤ dmax)
    (hell : ∀j,0< ell j) (hsmall : ∀j,ell j≤ dmin*mesh)
    (hsupply : (7/37)*dmax≤∑j,ell j) :
    (∀j,0< ell j/d) ∧ (∀j,ell j/d≤ mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0< d := hdmin.trans_le hd
  have hm : 0≤ mesh := by
    by_contra hn
    have hneg : mesh<0 := lt_of_not_ge hn
    have hsum : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hneg.le)
    have hmax : 0< dmax := hd0.trans_le hdmax
    nlinarith
  refine ⟨fun j=> div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div]
    apply (le_div_iff₀ hd0).mpr
    nlinarith
end
end OAI.SevenEighths.Cycle25WeightedHighRowFamily
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.SlotWidths -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.MomentData ; sha256 be25b9527e3b5824d2c91385d7a73c4c4e8ed05d456bfb15c97f80feb4161d2f -/
section

namespace Cycle25.Weighted
structure MomentData where
  N : ℕ
  ell : Fin N → ℝ
  t : ℝ
  ε : ℝ
  e : ℝ
  t_pos : 0 < t
  t_small : t ≤ 1/100000000
  slots_injective : Function.Injective ell
  slots_bounds : ∀j, 0 < ell j ∧ ell j ≤ 1
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1/1000
  e_pos : 0 < e
end Cycle25.Weighted

/- Adapted unchanged from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Assembly.MomentData -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.FirstSourceParameters ; sha256 8e96515a335d4e01dd1dbc32f048e5957f2ebb2adfee90479eb81b044d4a4b75 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/FirstSourceParameters.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/





namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentSectorLocalization

def sourceEpsilon (M A B ε:ℝ):ℝ:=reserve M B ε/(4*((A+1)+A+1))
def maskEpsilon (M B ε:ℝ):ℝ:=reserve M B ε/(B+B+1)
def columnLoss (M B ε:ℝ)(k:ℕ):ℝ:=
  stageLoss M B ε (k+1)-2*reserve M B ε-reserve M B ε/4

lemma source_cap_mono (es ds ts Bactual Bschedule sigma delta amp em child er θs θc κ mesh A saving:ℝ)
    (hB:Bactual≤ Bschedule)(ht:0≤ ts)(hem:0≤ em)(j:Fin 4):
    losses es ds ts Bactual j+
      lossVector sigma delta amp (sourcePaid Bactual em child er delta amp θs θc κ mesh) es A saving j≤
    losses es ds ts Bschedule j+
      lossVector sigma delta amp (sourcePaid Bschedule em child er delta amp θs θc κ mesh) es A saving j:=by
  fin_cases j <;>
    simp only [losses,lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hB),mul_nonneg hem (sub_nonneg.mpr hB)]

theorem parameter_gates (M A B κ ε:ℝ)(hM:0≤ M)(hA:0≤ A)(hB:0≤ B)
    (hκ:(7/10:ℝ)≤κ)(hε:0<ε):
    let sigma:=amplification ε
    let r:=reserve M B ε
    0< sigma ∧ sigma≤1 ∧ 0< r/4 ∧ r/4≤ sigma/4 ∧ r/4≤1 ∧
      0< sourceEpsilon M A B ε ∧ sourceEpsilon M A B ε≤1 ∧
      0< maskEpsilon M B ε ∧ 0< mesh M B κ ε ∧
      mesh M B κ ε≤ sigma/12 ∧ 0≤ sigma/12 ∧ sigma/12< sigma/6 ∧
      0<2*sigma+1 ∧ 0≤ A+1:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have hb:=bounds M B κ ε hM hB hκ0 hε
  have hr:=hb.2.2.2.1
  have hrs:reserve M B ε≤ amplification ε/100:=min_le_left _ _
  have hm:=hb.2.2.2.2.2.1
  have hes:0< sourceEpsilon M A B ε:=by unfold sourceEpsilon;positivity
  have hesr:sourceEpsilon M A B ε≤ reserve M B ε:=by
    unfold sourceEpsilon
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hr.le hA]
  exact ⟨hb.1,hb.2.1,by positivity,by linarith,by linarith,
    hes,by linarith,by unfold maskEpsilon;positivity,hb.2.2.2.2.1,
    by linarith,by linarith [hb.1],by linarith [hb.1],by linarith [hb.1],by linarith⟩

lemma columnLoss_physical (M B ε:ℝ)(k:ℕ):
    columnLoss M B ε k+reserve M B ε/4=
      CenteredMomentEnergyStageMargins.physicalLoss M B ε k:=by
  unfold columnLoss CenteredMomentEnergyStageMargins.physicalLoss
  ring

theorem eventually_actual_four_fit (M A P B κ ε:ℝ)
    (hM:0≤ M)(hA:0≤ A)(_hP:0≤ P)(hB:0≤ B)(hready:readyBudget A P≤ B)
    (hκ:(7/10:ℝ)≤κ)(hε:0<ε):
    let r:=reserve M B ε
    ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(k:ℕ)(εchild:ℝ),εchild≤ stageLoss M B ε k→∀j:Fin 4,
        losses (sourceEpsilon M A B ε) (r/4) (r/4) (readyBudget A P) j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            ((readyBudget A P+readyBudget A P)*maskEpsilon M B ε+εchild+r/4+
              (frequencyLoss Z 32 (r/4)+r/4+r/4)/6+(r/4)/3+κ*mesh M B κ ε)
            (sourceEpsilon M A B ε) A (2*amplification ε+1) j+
          sourceEpsilon M A B ε*(A+1)+r/4≤ columnLoss M B ε k:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have h:=actual_frequency_four_budget M A B (A+1) κ ε hM hA hB (by linarith) hκ0 hε
  obtain ⟨_,_,hem,_,_,hevent⟩:=h
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ0 hε).2.2.2.1
  filter_upwards [hevent] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro k εchild hchild j
  have hfit:=hZ.2.2.2 k εchild (reserve M B ε) (reserve M B ε) hchild le_rfl le_rfl j
  have hmono:=source_cap_mono (sourceEpsilon M A B ε) (reserve M B ε/4) (reserve M B ε/4)
    (readyBudget A P) B (amplification ε) (frequencyLoss Z 32 (reserve M B ε/4))
    (reserve M B ε/4) (maskEpsilon M B ε) εchild (reserve M B ε/4)
    (reserve M B ε/4) (reserve M B ε/4) κ (mesh M B κ ε) A (2*amplification ε+1)
    hready (by positivity) hem.le j
  change losses (sourceEpsilon M A B ε) _ _ B j+
    lossVector _ _ _ (sourcePaid B (maskEpsilon M B ε) εchild _ _ _ _ _ _ _) _ _ _ j+
    sourceEpsilon M A B ε*(A+1)+_+_+_+_≤_ at hfit
  dsimp only [sourcePaid] at hmono hfit
  unfold columnLoss
  dsimp only [sourceEpsilon,maskEpsilon] at hmono hfit ⊢
  linarith only [hmono,hfit]

theorem ready_budget_final (M Bmask L ε A P:ℝ)(hM:0≤ M)(hB:0≤ Bmask)
    (hA:A≤2*CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε)+M+1)
    (hP:P≤ Bmask):
    readyBudget A P≤ CenteredMomentEnergyWidthRanges.finalSourceCap M Bmask L ε:=by
  have hn:1≤ count M ε:=by
    unfold count CenteredMomentFirstSecondLossParameters.depth
    omega
  have hm:=CenteredMomentEnergyWidthRanges.range_mono M Bmask L hM hB hn
  have hr:20≤ CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε):=by
    simp only [CenteredMomentEnergyWidthRanges.range,CenteredMomentEnergyWidthRanges.step] at hm
    linarith [le_max_left (1:ℝ) L]
  unfold readyBudget CenteredMomentEnergyWidthRanges.finalSourceCap CenteredMomentEnergyWidthRanges.sourceCap
  linarith

end SevenEighths.Cycle25CenteredMomentEnergyFirstSourceParameters

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.FirstSourceParameters -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReflectionRetainedLength ; sha256 210a0fd97646a8c6fa82b64dec23d16055cd96032d1e6f8e618a6457e2fdca82 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Moments/ReflectionRetainedLength.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/



namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.Cycle25CenteredMomentReflectionRetainedLength
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma retained_scale_lower (R Y : ℝ) (hY : 0< Y) (n : ℤ)
    (hn : n∈retainedAnnuli R Y hY) : 1≤ dyadicScale n*Y := by
  obtain ⟨hr,q,hq,hne⟩ := (retainedAnnuli_mem R Y hY n).mp hn
  have hs := (dyadicWeight_support n hne).2.le
  have hh := mul_le_mul_of_nonneg_right (hq.trans hs) hY.le
  simpa only [inv_mul_cancel₀ hY.ne'] using hh

theorem eventually_actual_retained_length (C box xi : ℝ) (hC : 0< C)
    (hbox : 1≤ box) (hxi : 0< xi) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀(M a Q R d h : ℝ),
      0< Q → 0< d → Q*R≤ C*Z^M → d≤ R → 1≤ h →
      ∀n : ℤ,∀hY : 0< Q*d/(Z^a*h),
      n∈retainedAnnuli (Z^(xi/4)) (Q*d/(Z^a*h)) hY →
      1≤ dyadicScale n*(Q*d/(Z^a*h)) ∧
      0≤ Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h)))) ∧
      Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h))))≤ M-a+xi := by
  have hc := (tendsto_rpow_atTop (show 0< xi/2 by linarith)).eventually
    (eventually_ge_atTop (box*C))
  have hfour := (tendsto_rpow_atTop (show 0< xi/4 by linarith)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc,hfour] with Z hZ hconst h4
  refine ⟨hZ,?_⟩
  intro M a Q R d h hQ hd hcap hdR hh n hY hn
  have hz : 0< Z := zero_lt_one.trans hZ
  have hs : dyadicScale n≤ Z^(xi/2) := by
    calc
      _≤4*Z^(xi/4) := retained_scale_le _ n ((retainedAnnuli_mem _ _ hY n).mp hn).1
      _≤ Z^(xi/4)*Z^(xi/4) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=Z^(xi/2) := by rw [←Real.rpow_add hz];congr 1;ring
  have hlo := retained_scale_lower _ _ hY n hn
  have hraw := reflected_scale_bound Z M a xi C Q R d h (dyadicScale n)
    hZ hC.le hQ.le hd.le (dyadicScale_pos n).le hcap hdR hh hs
  have hb : 1≤ box*(dyadicScale n*(Q*d/(Z^a*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤_ :=mul_le_mul hbox hlo zero_le_one (by linarith)
  refine ⟨hlo,Real.logb_nonneg hZ hb,?_⟩
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hb)).mpr
  calc
    _≤ box*(C*Z^(M-a+xi/2)) := mul_le_mul_of_nonneg_left hraw (by linarith)
    _=(box*C)*Z^(M-a+xi/2) :=by ring
    _≤ Z^(xi/2)*Z^(M-a+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
    _=Z^(M-a+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

lemma one_reflection_total_width (M A z b xi reflected : ℝ)
    (hb : b≤ M/4) (hreflection : reflected≤ M-(A-z-b)+xi) :
    reflected+b+z≤3*M/2-A+2*z+xi := by linarith

lemma positive_slot_width_drop (M A z xi kappa : ℝ)
    (hM : 0≤ M) (hz : 0≤ z) (hk : 7/10≤ kappa)
    (hA : 5*M/6≤ A) (hcap : A+(6*kappa-1)*z≤ M) :
    3*M/2-A+2*z+xi≤37*M/48+xi ∧
    3*M/2-A+2*z+xi+(6*kappa-1)*z≤15*M/16+xi := by
  have hkz : 16/5*z≤(6*kappa-1)*z := mul_le_mul_of_nonneg_right (by linarith) hz
  have hsmall : z≤5*M/96 := by linarith
  constructor <;> nlinarith

end SevenEighths.Cycle25CenteredMomentReflectionRetainedLength

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReflectionRetainedLength -/
