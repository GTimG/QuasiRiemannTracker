/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountCrossing

/- BEGIN ORIGINAL Cycle25.Assembly.Count.Crossing; sha256 e62904966711721f3a59ecb04bfd36c708f5d0568eb9b1bdda3b2ef74b05bbf4 -/
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

lemma b_bounds {p κ : ℝ} (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    0≤b p κ ∧ 4*p/9≤b p κ ∧ b p κ≤10*p/21 ∧ b p κ≤p := by
  have hd : 0<3*κ := by linarith
  unfold b
  refine ⟨div_nonneg hp hd.le,(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_⟩
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hk1)]
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hk)]
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hk)]

lemma denominator_lower {p κ : ℝ} (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) : 85/42≤denominator p κ := by
  have hb := b_bounds hp hp1 hk hk1
  unfold denominator
  linarith

theorem crossing_bounds {p κ t : ℝ} (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (ht : 1≤t) (ht1 : t≤3/2) :
    23/37≤crossing p κ t ∧ crossing p κ t≤1 ∧
      1/3≤t-crossing p κ t ∧ t-crossing p κ t≤1/2 := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : 0<denominator p κ := lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1)
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

theorem selected_short_bound {δ p κ t r : ℝ} (hδ : 0≤δ) (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    (r≤crossing p κ t → plainExponent δ p κ t r≤shortExponent δ p κ t) ∧
      (crossing p κ t≤r → inverseExponent δ p r≤shortExponent δ p κ t) := by
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

lemma short_ge_base {δ p κ t : ℝ} (hδ : 0≤δ) (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (ht : t≤3/2) : 1-δ≤shortExponent δ p κ t := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : 0<denominator p κ := lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1)
  have hw : 0≤primeWeight p κ := by unfold primeWeight; exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  unfold shortExponent coefficient
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hδ (div_nonneg hw hd.le)) (by linarith))

theorem plain_capacity_comparison {δ p κ t r m γ : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤1) (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (hγ : 0≤γ) (hlength : t-r-γ≤m) :
    1-2*δ*m-2*(δ*p)*(1-2*m)/(6*κ)≤plainExponent δ p κ t r+2*γ := by
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
/- END ORIGINAL Cycle25.Assembly.Count.Crossing -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.Endpoint; sha256 3a49b221517994d59cbca8da2f61bc333603502f42201e317206b5e170dcd284 -/
section
                                      
namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section

def V (δ : ℝ) : ℝ := 5/6-δ
def cutoff (δ p κ : ℝ) : ℝ := 1+δ*coefficient p κ/(2*(V δ+δ*coefficient p κ))
def rowCount (δ p κ : ℝ) : ℝ :=
  1-δ+δ*coefficient p κ*V δ/(2*(V δ+δ*coefficient p κ))

lemma coefficient_nonneg {p κ : ℝ} (hp : 0≤p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) : 0≤coefficient p κ := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : 0<denominator p κ := lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1)
  unfold coefficient primeWeight
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) hd.le

lemma cutoff_bounds {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    1≤cutoff δ p κ ∧ cutoff δ p κ≤3/2 := by
  have hc := coefficient_nonneg hp hp1 hk hk1
  have hn : 0≤δ*coefficient p κ := mul_nonneg hδ hc
  have hv : 0<V δ := by unfold V; linarith
  have hd : 0<2*(V δ+δ*coefficient p κ) := by positivity
  unfold cutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hn hd.le)
  · have he : δ*coefficient p κ/(2*(V δ+δ*coefficient p κ))≤1/2 :=
      (div_le_iff₀ hd).mpr (by linarith)
    linarith

theorem short_at_cutoff {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    shortExponent δ p κ (cutoff δ p κ)=rowCount δ p κ := by
  have hc := coefficient_nonneg hp hp1 hk hk1
  have hd : V δ+δ*coefficient p κ≠0 := by
    apply ne_of_gt
    have hv : 0<V δ := by unfold V; linarith
    exact add_pos_of_pos_of_nonneg hv (mul_nonneg hδ hc)
  unfold shortExponent cutoff rowCount
  field_simp
  ring

theorem long_at_cutoff {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    longExponent δ (cutoff δ p κ)=rowCount δ p κ := by
  have hc := coefficient_nonneg hp hp1 hk hk1
  have hd : V δ+δ*coefficient p κ≠0 := by
    apply ne_of_gt
    have hv : 0<V δ := by unfold V; linarith
    exact add_pos_of_pos_of_nonneg hv (mul_nonneg hδ hc)
  unfold longExponent HeckeDetectorRowCount.longExponent cutoff rowCount V at *
  field_simp
  ring

theorem max_at_cutoff {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    max (shortExponent δ p κ (cutoff δ p κ)) (longExponent δ (cutoff δ p κ))=rowCount δ p κ := by
  rw [short_at_cutoff hδ hδ1 hp hp1 hk hk1,long_at_cutoff hδ hδ1 hp hp1 hk hk1,max_self]
end
end OAI.SevenEighths.Cycle25DetectorRowCount

end
/- END ORIGINAL Cycle25.Assembly.Count.Endpoint -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.Budget; sha256 e38c45d009427ad135e5f99b5c9698e186565d120507e02339501099c1d312f6 -/
section
                                      

namespace OAI

noncomputable section
namespace SevenEighths.Cycle25DetectorBranchBudget
open Cycle25DetectorRowCount

def commonLoss (ε εm mesh ν : ℝ) : ℝ := 154*ε+εm+mesh+ν

theorem no_slot_inverse_loss (r δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : 0≤mesh) (hν : 0≤ν) :
    max 1 ((1+5*r)/6)-δ*r+2*ε+εm≤
      max 1 ((1+5*r)/6)-δ*r+commonLoss ε εm mesh ν := by
  unfold commonLoss
  linarith

theorem no_slot_plain_loss (m δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : m≤1/2+75*ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    max 1 (2*m)-2*δ*m+4*ε+εm≤1-2*δ*m+commonLoss ε εm mesh ν := by
  have hx : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith)
  unfold commonLoss
  linarith

theorem inverse_marked_loss (r δ x ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-δ*r-2*(δ*x)*((1-r)/2-ν)+2*ε+δ*mesh+εm≤
      inverseExponent δ x r+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold inverseExponent commonLoss
  nlinarith

theorem plain_marked_loss (m δ x κ ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-2*δ*m-2*(δ*x)*((1-2*m)/(6*κ)-ν)+4*ε+δ*mesh+εm≤
      1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ)+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold commonLoss
  have heq : 2*(δ*x)*((1-2*m)/(6*κ)-ν)=
      2*(δ*x)*(1-2*m)/(6*κ)-2*(δ*x)*ν := by ring
  rw [heq]
  linarith

theorem inverse_requested_capacity (r ν : ℝ) (hr : 23/37≤r) (_hr1 : r<1)
    (hν : 0<ν) (hνcap : ν<(1-r)/2) :
    0≤(1-r)/2-ν ∧ (1-r)/2-ν≤7/37 ∧
      r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem plain_requested_capacity (κ x t r m ε ν : ℝ)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (hx : 0≤x) (hx1 : x≤1/2) (ht : 1≤t) (ht1 : t≤3/2)
    (hr : r≤crossing x κ t) (hleft : t-r-ε≤m) (hε : ε≤1/12)
    (hν : 0≤ν) (hνcap : ν<(1-2*m)/(6*κ)) :
    0≤(1-2*m)/(6*κ)-ν ∧ (1-2*m)/(6*κ)-ν≤7/37 ∧
      2*m+6*κ*((1-2*m)/(6*κ)-ν)≤1 := by
  have hcross := crossing_bounds hx hx1 hk hk1 ht ht1
  have hm : 1/4≤m := by linarith [hcross.2.2.1]
  have hd : 0<6*κ := by linarith
  have hc : (1-2*m)/(6*κ)≤5/42 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith,by linarith,?_⟩
  rw [mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end SevenEighths.Cycle25DetectorBranchBudget
end
end OAI

end
/- END ORIGINAL Cycle25.Assembly.Count.Budget -/

/- BEGIN ORIGINAL Cycle25.Assembly.Count.Moments; sha256 f4b63486416cf74c845e12a87ef145c550dba8c0dcd0b199cfacb52ba91ff113 -/
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
          F.physicalProduct selected u‖^2≤C*U^(1+εm)

theorem plain_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {κplain c κinverse C height εm : ℝ} (moments : Moments F κplain c κinverse C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hκ : 0≤κplain) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap : 2*F.m+6*κplain*z≤1) :
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
        (U^F.r) s t*F.physicalProduct selected u‖^2≤C*U^(1+εm)
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
          F.physicalProduct selected u‖^2≤C*U^(1+εm)


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
/- END ORIGINAL Cycle25.Assembly.Count.Moments -/
