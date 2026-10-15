/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B000
import Submissions.cycle61_c0125139.Bundles.B050
import Submissions.cycle61_c0125139.Bundles.B059
import Mathlib.Tactic.FieldSimp
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowCount

/- BEGIN ORIGINAL Cycle61.Physical.Capacity; sha256 c45c646a6c99f552d42fd070e752c105dac8809f1c7f3f084e171c76deeab5a1 -/
section
                                       
                               

namespace Cycle61.Physical

open Arithmetic

noncomputable section

def plainScale (d t : ℝ) : ℝ := 1 - y / d + t
def affineCapacity (d t : ℝ) : ℝ := (B - 2 * plainScale d t) / lambda
def shiftBase (d : ℝ) : ℝ := 2 * y / d - 1
def oldCapacity (b t : ℝ) : ℝ := max 0 ((b - 2 * t) / (9 / 2))
def shiftReserve (b t : ℝ) : ℝ :=
  t / 2 - (1 / 4) * ((b - (1 - B)) / lambda - oldCapacity b t)

theorem physical_d_pos {d : ℝ} (hd : dMinus ≤ d) : 0 < d := by
  have := half_lt_dMinus
  linarith

theorem plainScale_exact_bounds {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    5001680000 / 11894213961 ≤ plainScale d t ∧
      plainScale d t ≤ 402287137237 / 952737117000 := by
  have hy : 0 ≤ y := by norm_num [y]
  have hdm : 0 < dMinus := by norm_num [dMinus]
  have hdp := physical_d_pos hd.1
  have hhi := div_le_div_of_nonneg_left hy hdm hd.1
  have hlo := div_le_div_of_nonneg_left hy hdp hd.2
  norm_num [y, dMinus, dPlus, t0, plainScale] at *
  constructor <;> linarith

theorem plainScale_interior {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    41 / 100 < plainScale d t ∧ plainScale d t < 264 / 625 := by
  have hn := plainScale_exact_bounds hd ht
  constructor <;> linarith

theorem affineCapacity_exact_bounds {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    65807969436717121 / 1839925920350400000 ≤ affineCapacity d t ∧
      affineCapacity d t ≤ 841262571937768693 / 22970106001483200000 := by
  have hn := plainScale_exact_bounds hd ht
  unfold affineCapacity
  norm_num [B, lambda] at *
  constructor <;> linarith

theorem affineCapacity_interior {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    17 / 500 < affineCapacity d t ∧ affineCapacity d t < 37 / 1000 := by
  have hz := affineCapacity_exact_bounds hd ht
  constructor <;> linarith

theorem affineCapacity_budget (d t : ℝ) :
    2 * plainScale d t + lambda * affineCapacity d t = B := by
  unfold affineCapacity
  norm_num [lambda]
  ring

theorem scaled_capacity_zero {d : ℝ} (hd : d ≠ 0) :
    d * affineCapacity d 0 = (2 * y - (2 - B) * d) / lambda := by
  unfold affineCapacity plainScale
  field_simp [hd]
  ring

theorem affineCapacity_shift (d t : ℝ) :
    affineCapacity d 0 - affineCapacity d t = 2 * t / lambda := by
  unfold affineCapacity plainScale
  ring

theorem small_slot_shortening {n1 n2 z : ℝ}
    (h1 : n1 ≤ 264 / 625) (h2 : n2 ≤ 264 / 625) (hz : z ≤ 17 / 500) :
    n1 + n2 + (9 / 2) * z ≤ 1 - 11 / 5000 := by
  have := small_slot_complement
  linarith

theorem small_plain_shortening {n1 n2 z : ℝ}
    (h1 : n1 ≤ 41 / 100) (h2 : n2 ≤ 264 / 625) (hz : z ≤ 37 / 1000) :
    n1 + n2 + (9 / 2) * z ≤ 1 - 11 / 10000 := by
  have := small_plain_complement
  linarith

theorem affine_shortening {d t n1 n2 z : ℝ}
    (h1 : n1 ≤ plainScale d t) (h2 : n2 ≤ plainScale d t)
    (hz : z ≤ affineCapacity d t) : n1 + n2 + lambda * z ≤ B := by
  have hmul := mul_le_mul_of_nonneg_left hz (le_of_lt lambda_pos)
  have := affineCapacity_budget d t
  linarith

theorem positive_supply {d : ℝ} (hd : dMinus ≤ d ∧ d ≤ dPlus) :
    4 / 21 < ell / d := by
  have hy : 0 ≤ ell := le_of_lt ell_pos
  have hdiv := div_le_div_of_nonneg_left hy (physical_d_pos hd.1) hd.2
  have := supply_lower
  linarith

theorem capacity_supply {d t : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ht : 0 ≤ t ∧ t ≤ t0) :
    1269281592530944914352773973 / 9188042400593280000000000000 ≤
      ell - d * affineCapacity d t := by
  have hz := affineCapacity_exact_bounds hd ht
  have hzp : 0 ≤ affineCapacity d t := by linarith
  have hdp : 0 ≤ dPlus := by norm_num [dPlus]
  have hprod := mul_le_mul hd.2 hz.2 hzp hdp
  norm_num [dPlus, ell] at *
  linarith

theorem small_shift_paid {t q delta : ℝ}
    (ht : 0 ≤ t) (hq : q ≤ delta / 2) (hd : 0 ≤ delta) :
    t * q / lambda ≤ delta * t / 2 := by
  have hmul := mul_le_mul_of_nonneg_left hq ht
  have hnonneg : 0 ≤ delta * t := mul_nonneg hd ht
  norm_num [lambda] at *
  nlinarith

theorem shiftBase_bounds {d : ℝ} (hd : dMinus ≤ d ∧ d ≤ dPlus) :
    0 ≤ shiftBase d ∧ shiftBase d ≤ 1890853961 / 11894213961 ∧
      shiftBase d < 4 / 25 := by
  have hy : 0 ≤ y := by norm_num [y]
  have hdm : 0 < dMinus := by norm_num [dMinus]
  have hhi := div_le_div_of_nonneg_left hy hdm hd.1
  have hlo := div_le_div_of_nonneg_left hy (physical_d_pos hd.1) hd.2
  have hi_eq : y / dMinus = 6892533961 / 11894213961 := by norm_num [y, dMinus]
  have lo_eq : y / dPlus = 13785067922 / 23818427925 := by norm_num [y, dPlus]
  rw [hi_eq] at hhi
  rw [lo_eq] at hlo
  have base_eq : shiftBase d = 2 * (y / d) - 1 := by unfold shiftBase; ring
  rw [base_eq]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem shiftReserve_unclipped {b t : ℝ} (ht : 2 * t ≤ b) :
    shiftReserve b t = (7 / 18) * t + b / 18 - (b - (1 - B)) / (4 * lambda) := by
  have hnonneg : 0 ≤ (b - 2 * t) / (9 / 2) := by linarith
  unfold shiftReserve oldCapacity
  rw [max_eq_right hnonneg]
  ring

theorem shiftReserve_clipped {b t : ℝ} (ht : b ≤ 2 * t) :
    shiftReserve b t = t / 2 - (b - (1 - B)) / (4 * lambda) := by
  have hnonpos : (b - 2 * t) / (9 / 2) ≤ 0 := by linarith
  unfold shiftReserve oldCapacity
  rw [max_eq_left hnonpos]
  ring

theorem oldCapacity_nonneg (b t : ℝ) : 0 ≤ oldCapacity b t := le_max_left _ _

theorem oldCapacity_zero {b t : ℝ} (ht : b ≤ 2 * t) : oldCapacity b t = 0 := by
  unfold oldCapacity
  apply max_eq_left
  linarith

theorem oldCapacity_budget (b t : ℝ) :
    1 - b + 2 * t + (9 / 2) * oldCapacity b t = max 1 (1 - b + 2 * t) := by
  by_cases ht : b ≤ 2 * t
  · rw [oldCapacity_zero ht, max_eq_right (by linarith : 1 ≤ 1 - b + 2 * t)]
    ring
  · have hc : 0 ≤ (b - 2 * t) / (9 / 2) := by linarith
    unfold oldCapacity
    rw [max_eq_right hc, max_eq_left (by linarith : 1 - b + 2 * t ≤ 1)]
    ring

theorem shiftReserve_unclipped_slope {b t1 t2 : ℝ}
    (h1 : 2 * t1 ≤ b) (h2 : 2 * t2 ≤ b) :
    shiftReserve b t2 - shiftReserve b t1 = (7 / 18) * (t2 - t1) := by
  rw [shiftReserve_unclipped h1, shiftReserve_unclipped h2]
  ring

theorem shiftReserve_clipped_slope {b t1 t2 : ℝ}
    (h1 : b ≤ 2 * t1) (h2 : b ≤ 2 * t2) :
    shiftReserve b t2 - shiftReserve b t1 = (1 / 2) * (t2 - t1) := by
  rw [shiftReserve_clipped h1, shiftReserve_clipped h2]
  ring

theorem large_shift_reserve {b t : ℝ} (hb : b ≤ 4 / 25) (ht : t0 ≤ t) :
    4035883 / 69523200000 ≤ shiftReserve b t := by
  by_cases hclip : b ≤ 2 * t
  · rw [shiftReserve_clipped hclip]
    norm_num [B, lambda, t0] at *
    linarith
  · have hu : 2 * t ≤ b := le_of_lt (lt_of_not_ge hclip)
    rw [shiftReserve_unclipped hu]
    norm_num [B, lambda, t0] at *
    linarith

theorem large_shift_paid {b t q delta : ℝ}
    (hb : b ≤ 4 / 25) (ht : t0 ≤ t) (hq0 : 0 ≤ q)
    (hq : q ≤ delta / 2) (hd : 0 ≤ delta) :
    (q / 2) * ((b - (1 - B)) / lambda - oldCapacity b t) ≤ delta * t / 2 := by
  let loss := (b - (1 - B)) / lambda - oldCapacity b t
  have hreserve := large_shift_reserve hb ht
  change 4035883 / 69523200000 ≤ t / 2 - (1 / 4) * loss at hreserve
  have hloss : loss ≤ 2 * t := by linarith
  have htp : 0 ≤ t := by norm_num [t0] at ht; linarith
  change (q / 2) * loss ≤ delta * t / 2
  by_cases hnonneg : 0 ≤ loss
  · have hqmul := mul_le_mul_of_nonneg_right hq hnonneg
    have hdmul := mul_le_mul_of_nonneg_left hloss hd
    nlinarith
  · have hleft : q * loss ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0 (le_of_not_ge hnonneg)
    have hright := mul_nonneg hd htp
    nlinarith

end

end Cycle61.Physical

end
/- END ORIGINAL Cycle61.Physical.Capacity -/

/- BEGIN ORIGINAL Cycle61.Numerator.Capacity.Schedule; sha256 b1256dbc4d92e48f0a52c1cfab887bfc653749c67a92da959cc1c92fad036ea0 -/
section
                                

namespace Cycle61.Numerator.Capacity

open Cycle61.Arithmetic

noncomputable section

def zeroCapacity (d : ℝ) : ℝ := Physical.affineCapacity d 0

def scheduledCapacity (d v : ℝ) : ℝ :=
  if v ≤ 2*t0 then Physical.affineCapacity d (v/2)
  else Physical.oldCapacity (Physical.shiftBase d) (v/2)

def dampingRate : ℝ := 1/1000

theorem dampingRate_pos : 0 < dampingRate := by norm_num [dampingRate]

theorem zeroCapacity_eq_shiftBase (d : ℝ) :
    zeroCapacity d = (Physical.shiftBase d-(1-B))/lambda := by
  unfold zeroCapacity Physical.affineCapacity Physical.plainScale Physical.shiftBase
  ring

theorem scaled_zeroCapacity {d : ℝ} (hd : d ≠ 0) :
    d*zeroCapacity d = (2*y-(2-B)*d)/lambda :=
  Physical.scaled_capacity_zero hd

theorem scheduledCapacity_le_supply {d v : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v) :
    scheduledCapacity d v ≤ ell/d := by
  unfold scheduledCapacity
  split_ifs with hsmall
  · have hcap := Physical.capacity_supply hd
      (show 0 ≤ v/2 ∧ v/2 ≤ t0 by constructor <;> linarith)
    apply (le_div_iff₀ (Physical.physical_d_pos hd.1)).mpr
    nlinarith
  · have hb := (Physical.shiftBase_bounds hd).2.2
    have hcap : Physical.oldCapacity (Physical.shiftBase d) (v/2) ≤ 8/225 := by
      unfold Physical.oldCapacity
      apply max_le
      · norm_num
      · linarith
    have hsupply := Physical.positive_supply hd
    linarith

theorem scheduledCapacity_nonneg {d v : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v) : 0 ≤ scheduledCapacity d v := by
  unfold scheduledCapacity
  split_ifs with hsmall
  · have hz := Physical.affineCapacity_interior hd
      (show 0 ≤ v/2 ∧ v/2 ≤ t0 by constructor <;> linarith)
    linarith [hz.1]
  · exact Physical.oldCapacity_nonneg _ _

theorem scheduled_small_budget {d v : ℝ} (hsmall : v ≤ 2*t0) :
    2*Physical.plainScale d (v/2)+lambda*scheduledCapacity d v = B := by
  rw [scheduledCapacity, ite_eq_left hsmall]
  exact Physical.affineCapacity_budget d (v/2)

theorem scheduled_large_budget {d v : ℝ} (hlarge : 2*t0 < v) :
    1-Physical.shiftBase d+v+(9/2)*scheduledCapacity d v =
      max 1 (1-Physical.shiftBase d+v) := by
  rw [scheduledCapacity, ite_eq_right (not_le.mpr hlarge)]
  have hh := Physical.oldCapacity_budget (Physical.shiftBase d) (v/2)
  rwa [show 2*(v/2) = v by ring] at hh

theorem large_shift_proportional_reserve {b t : ℝ}
    (hb : b ≤ 4/25) (ht : t0 ≤ t) : t/500 ≤ Physical.shiftReserve b t := by
  by_cases hclip : b ≤ 2*t
  · rw [Physical.shiftReserve_clipped hclip]
    norm_num [B, lambda, t0] at *
    linarith
  · have hu : 2*t ≤ b := le_of_lt (lt_of_not_ge hclip)
    rw [Physical.shiftReserve_unclipped hu]
    norm_num [B, lambda, t0] at *
    linarith

theorem scheduled_capacity_damping {d v q delta : ℝ}
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hdelta : 0 ≤ delta) :
    q*zeroCapacity d/2+dampingRate*delta*v ≤
      delta*v/4+q*scheduledCapacity d v/2 := by
  by_cases hsmall : v ≤ 2*t0
  · rw [scheduledCapacity, ite_eq_left hsmall]
    have hid := Physical.affineCapacity_shift d (v/2)
    change zeroCapacity d-Physical.affineCapacity d (v/2) = 2*(v/2)/lambda at hid
    have hm := mul_nonneg (sub_nonneg.mpr hqdelta) hv
    have hnonneg := mul_nonneg hdelta hv
    norm_num [lambda, dampingRate] at hid ⊢
    nlinarith
  · rw [scheduledCapacity, ite_eq_right hsmall]
    have ht : t0 ≤ v/2 := by linarith [lt_of_not_ge hsmall]
    have hb : Physical.shiftBase d ≤ 4/25 := (Physical.shiftBase_bounds hd).2.2.le
    have hreserve := large_shift_proportional_reserve hb ht
    rw [Physical.shiftReserve, ← zeroCapacity_eq_shiftBase d] at hreserve
    let loss := zeroCapacity d-Physical.oldCapacity (Physical.shiftBase d) (v/2)
    have ht0 : 0 ≤ v/2 := by linarith
    change (v/2)/500 ≤ (v/2)/2-(1/4)*loss at hreserve
    change q*zeroCapacity d/2+dampingRate*delta*v ≤
      delta*v/4+q*Physical.oldCapacity (Physical.shiftBase d) (v/2)/2
    by_cases hloss : 0 ≤ loss
    · have hqmul := mul_le_mul_of_nonneg_right hqdelta hloss
      have hdmul := mul_le_mul_of_nonneg_left hreserve hdelta
      dsimp only [loss] at hqmul hdmul
      norm_num [dampingRate] at *
      nlinarith
    · have hqmul := mul_nonpos_of_nonneg_of_nonpos hq (le_of_not_ge hloss)
      have hdmul := mul_nonneg hdelta hv
      dsimp only [loss] at hqmul
      norm_num [dampingRate]
      nlinarith

end
end Cycle61.Numerator.Capacity

end
/- END ORIGINAL Cycle61.Numerator.Capacity.Schedule -/

/- BEGIN ORIGINAL Cycle61.Numerator.Fourth.Geometry; sha256 9b213fb739da4f2dfccea43e11f2a1708ec53d303ee57a70ea675d50d19452d4 -/
section
                                          
                                    

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace Cycle61.Numerator.Fourth
open Cycle61.Arithmetic
open Cycle25.Numerator

lemma physical_y_range {d : ℝ} (hd : dMinus≤ d ∧ d≤ dPlus) :
    1/2≤ y/d ∧ y/d<1 := by
  have hs:=Physical.shiftBase_bounds hd
  have hp:=Physical.physical_d_pos hd.1
  refine ⟨by unfold Physical.shiftBase at hs;rw [mul_div_assoc] at hs;linarith,?_⟩
  apply (div_lt_one hp).mpr
  exact y_lt_half.trans (half_lt_dMinus.trans_le hd.1)

lemma coefficient_box_geometry {d xi slack : ℝ} (hd : dMinus≤ d ∧ d≤ dPlus)
    (hx : 0<xi) (hs : 0≤ slack) (hsmall : 2*xi+slack≤1/2)
    (j : ℕ) (hj : j∈Finset.range (coefficientBoxCount xi+1)) :
    0≤1-y/d+(j:ℝ)*xi+xi ∧ (1-y/d+(j:ℝ)*xi+xi)+slack≤2 := by
  have hy:=physical_y_range hd
  have hv:=coefficient_box_index_range xi hx j hj
  constructor <;> linarith

/-- A physical logarithmic conductor shift v enters the two-plain budget as
2v. This exact factor is retained in the public selected-capacity argument. -/
lemma scheduled_capacity_or_empty {α : Type*} (T : Finset α) (width : T→ℝ)
    {d t κ : ℝ} (hd : dMinus≤ d ∧ d≤ dPlus) (ht : 0≤ t) (hk : κ≤3/4)
    (hw : ∀i,0<width i)
    (hselected : (∑i,width i)≤ Capacity.scheduledCapacity d (2*t)) :
    (∃d' t':ℝ,dMinus≤ d' ∧ d'≤ dPlus ∧ 0≤ t' ∧ t'≤ t0 ∧
      Physical.plainScale d t=Physical.plainScale d' t' ∧
      (∑i,width i)≤ Physical.affineCapacity d' t') ∨
      (2*Physical.plainScale d t+6*κ*(∑i,width i)≤1 ∨ T=∅) := by
  have hsum:0≤∑i,width i:=Finset.sum_nonneg (fun i _=>(hw i).le)
  by_cases hsmall:t≤ t0
  · left
    refine ⟨d,t,hd.1,hd.2,ht,hsmall,rfl,?_⟩
    simpa [Capacity.scheduledCapacity,show 2*t≤2*t0 by linarith] using hselected
  · right
    have hlarge:¬2*t≤2*t0:=by linarith
    have hselected':(∑i,width i)≤ Physical.oldCapacity (Physical.shiftBase d) t:=by
      simpa [Capacity.scheduledCapacity,hlarge] using hselected
    by_cases hraw:0≤(Physical.shiftBase d-2*t)/(9/2)
    · left
      have hs:(∑i,width i)≤(Physical.shiftBase d-2*t)/(9/2):=by
        simpa [Physical.oldCapacity,max_eq_right hraw] using hselected'
      have hbudget:2*Physical.plainScale d t+(9/2)*(∑i,width i)≤1:=by
        unfold Physical.plainScale Physical.shiftBase at *
        rw [mul_div_assoc] at hs
        linarith
      nlinarith
    · right
      have hs:(∑i,width i)≤0:=by
        simpa [Physical.oldCapacity,max_eq_left (le_of_not_ge hraw)] using hselected'
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hs':width ⟨i,hi⟩≤∑i,width i:=Finset.single_le_sum
        (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
      linarith [hw ⟨i,hi⟩]

end Cycle61.Numerator.Fourth

end
/- END ORIGINAL Cycle61.Numerator.Fourth.Geometry -/

/- BEGIN ORIGINAL Cycle25.Energy.Physical.Discarded; sha256 05e6dc579e2614d20adf8865f778e4af74937a01fc8f6a4ea2e25689b454db06 -/
section
                                              
                                                     

noncomputable section
set_option maxHeartbeats 800000
open scoped Classical BigOperators SchwartzMap
namespace Cycle25.Weighted.Numerator.PhysicalTail
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentUniformReflectionApproximation CenteredMomentNaturalPrimitive
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectionMass
local notation "O" => HeckeFamily.O

/-- The exact coefficient cutoff bounds every discarded dual length uniformly.
Neither a scale-bin assumption nor a pointwise critical-line L-bound is needed. -/
theorem discardedSchwartz_active_negligible (xi saving epsilon b Ccond : ℝ)
    (hxi : 0<xi) (heps : 0<epsilon) (hb : 0<b) (hCcond : 0<Ccond) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(τ ψ : Character)(G : 𝓢(ℝ,ℂ))(Y N U : ℝ),
      0<Y → 0<N → N≤b*Y → 1≤U →
      (ψ.modulus.absNorm:ℝ)*(redundantIdeal τ.modulus ψ.modulus).absNorm≤Ccond*U →
      ‖discardedSchwartz τ ψ G (Y/N) (U^(xi/2))‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*U^(epsilon-saving) := by
  obtain ⟨H,C,hC,hbound⟩ := deleted_discarded_negligible xi saving 1 (b*Ccond) epsilon
    hxi (mul_pos hb hCcond) heps
  refine ⟨H,C*Ccond^epsilon,by positivity,?_⟩
  intro τ ψ G Y N U hY hN hcut hU hcap
  let S := redundantSet τ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hQone : (1:ℝ)≤ψ.modulus.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hnorm : (Ideal.absNorm (∏P∈S,P):ℝ)≤Ccond*U := by
    have hr : 0≤(Ideal.absNorm (∏P∈S,P):ℝ) := by positivity
    have hl := mul_le_mul_of_nonneg_right hQone hr
    exact (show (Ideal.absNorm (∏P∈S,P):ℝ)≤(ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ) by simpa only [one_mul] using hl).trans hcap
  have hYX : 1≤b*(Y/N) := by
    rw [←mul_div_assoc,le_div_iff₀ hN]
    simpa using hcut
  have hscale : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤
      (b*Ccond)*U^(1:ℝ)*(Y/N) := by
    calc
      _ ≤ Ccond*U := hcap
      _ ≤ (Ccond*U)*(b*(Y/N)) := le_mul_of_one_le_right (by positivity) hYX
      _ = _ := by rw [Real.rpow_one];ring
  have hh := (hbound G S hS ψ ψ.inverse τ.inverse (ψ.modulus.absNorm:ℝ) (Y/N) U
    hU hQ (div_pos hY hN) hscale).2
  change ‖discardedSchwartz τ ψ G (Y/N) (U^(xi/2))‖≤_ at hh
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hU0 : 0<U := zero_lt_one.trans_le hU
  calc
    _ ≤ C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        (Ideal.absNorm (∏P∈S,P):ℝ)^epsilon*U^(-saving) := hh
    _ ≤ C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Ccond*U)^epsilon*U^(-saving) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hCcond.le hU0.le,Real.rpow_sub hU0]
      rw [Real.rpow_neg hU0.le]
      ring


/-- Once the physical profile is fixed, the complete discarded packet has an
arbitrary inverse-power bound at every active coefficient scale. -/
theorem discardedSchwartz_fixed_profile (xi saving b Ccond : ℝ)
    (hxi : 0<xi) (hb : 0<b) (hCcond : 0<Ccond) (G : 𝓢(ℝ,ℂ)) :
    ∃C : ℝ,0<C ∧ ∀(τ ψ : Character)(Y N U : ℝ),
      0<Y → 0<N → N≤b*Y → 1≤U →
      (ψ.modulus.absNorm:ℝ)*(redundantIdeal τ.modulus ψ.modulus).absNorm≤Ccond*U →
      ‖discardedSchwartz τ ψ G (Y/N) (U^(xi/2))‖≤C*U^(-saving) := by
  obtain ⟨H,C,hC,hbound⟩ := discardedSchwartz_active_negligible xi (saving+1) 1 b Ccond
    hxi (by norm_num) hb hCcond
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  refine ⟨C*(H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G+1),by positivity,?_⟩
  intro τ ψ Y N U hY hN hcut hU hcap
  have hh := hbound τ ψ G Y N U hY hN hcut hU hcap
  rw [show (1:ℝ)-(saving+1) = -saving by ring] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G+1) hC.le) (by positivity))

lemma fourth_norm_add (a b : ℂ) : ‖a+b‖^4≤8*(‖a‖^4+‖b‖^4) := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 4).trans
    (by convert add_pow_le (norm_nonneg a) (norm_nonneg b) 4 using 1 <;> norm_num)

theorem weighted_fourth_add {ι : Type*} (s : Finset ι) (R T Q : ι→ℂ) (Er Et : ℝ)
    (hr : (∑i∈s,‖R i‖^4*‖Q i‖^2)≤Er)
    (ht : (∑i∈s,‖T i‖^4*‖Q i‖^2)≤Et) :
    (∑i∈s,‖R i+T i‖^4*‖Q i‖^2)≤8*(Er+Et) := by
  calc
    _ ≤ ∑i∈s,8*(‖R i‖^4+‖T i‖^4)*‖Q i‖^2 :=
      Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (fourth_norm_add _ _) (sq_nonneg _))
    _ = 8*((∑i∈s,‖R i‖^4*‖Q i‖^2)+(∑i∈s,‖T i‖^4*‖Q i‖^2)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,add_mul,mul_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
    _ ≤ _ := by linarith

/-- Polynomial pointwise tails are negligible even with all selected factors. -/
theorem selected_tail_fourth {ι : Type*} (s : Finset ι) (T Q : ι→ℂ)
    (U r q saving Ccard Ctail Cslot : ℝ) (hU : 0<U)
    (hc : 0≤Ccard) (ht : 0≤Ctail) (hq : 0≤Cslot)
    (hcard : (s.card:ℝ)≤Ccard*U^r)
    (htail : ∀i∈s,‖T i‖≤Ctail*U^(-saving))
    (hslot : ∀i∈s,‖Q i‖≤Cslot*U^q) :
    (∑i∈s,‖T i‖^4*‖Q i‖^2)≤Ccard*Ctail^4*Cslot^2*U^(r+2*q-4*saving) := by
  calc
    _ ≤ ∑i∈s,(Ctail*U^(-saving))^4*(Cslot*U^q)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (htail i hi) 4)
        (pow_le_pow_left₀ (norm_nonneg _) (hslot i hi) 2) (sq_nonneg _) (by positivity)
    _ = (s.card:ℝ)*((Ctail*U^(-saving))^4*(Cslot*U^q)^2) := by simp
    _ ≤ (Ccard*U^r)*((Ctail*U^(-saving))^4*(Cslot*U^q)^2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have hpow (e : ℝ) (n : ℕ) : (U^e)^n=U^(e*n) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
      rw [mul_pow,mul_pow,hpow,hpow]
      calc
        _ = Ccard*Ctail^4*Cslot^2*(U^r*U^(-saving*4)*U^(q*2)) := by ring
        _ = _ := by rw [←Real.rpow_add hU,←Real.rpow_add hU];congr 2;ring


/-- The crude lattice count alone suffices for all discarded selected moments;
its constant is independent of any source-moment constant C0. -/
theorem row_discarded_fourth_negligible (xi saving q b Ccond Cslot : ℝ)
    (hxi : 0<xi) (hb : 0<b) (hCcond : 0<Ccond) (hslot0 : 0<Cslot)
    (G : 𝓢(ℝ,ℂ)) :
    ∃C : ℝ,0<C ∧ ∀(rows : Finset FreeRow)(τ ψ : FreeRow→Character)
      (N : FreeRow→ℝ)(Q : FreeRow→ℂ)(Y U : ℝ),
      0<Y → 1≤U → (∀u∈rows,0<N u ∧ N u≤b*Y) →
      (∀u∈rows,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤U) →
      (∀u∈rows,((ψ u).modulus.absNorm:ℝ)*
        (redundantIdeal (τ u).modulus (ψ u).modulus).absNorm≤Ccond*U) →
      (∀u∈rows,‖Q u‖≤Cslot*U^q) →
      (∑u∈rows,‖discardedSchwartz (τ u) (ψ u) G (Y/N u) (U^(xi/2))‖^4*‖Q u‖^2)≤C*U^(-saving) := by
  let s : ℝ := (1+2*q+saving)/4
  obtain ⟨C,hC,hbound⟩ := discardedSchwartz_fixed_profile xi s b Ccond hxi hb hCcond G
  refine ⟨128*C^4*Cslot^2,by positivity,?_⟩
  intro rows τ ψ N Q Y U hY hU hN hrows hcap hslot
  have hh := selected_tail_fourth rows
    (fun u=>discardedSchwartz (τ u) (ψ u) G (Y/N u) (U^(xi/2))) Q
    U 1 q s 128 C Cslot (zero_lt_one.trans_le hU) (by norm_num) hC.le hslot0.le
    (by simpa using ProbeHighRowFamily.freeRow_count rows U hU hrows)
    (fun u hu=>hbound (τ u) (ψ u) Y (N u) U hY (hN u hu).1 (hN u hu).2 hU (hcap u hu)) hslot
  convert hh using 1
  dsimp only [s]
  congr 2
  ring


theorem subtype_discarded_fourth_negligible (xi saving q b Ccond Cslot : ℝ)
    (hxi : 0<xi) (hb : 0<b) (hCcond : 0<Ccond) (hslot0 : 0<Cslot)
    (G : 𝓢(ℝ,ℂ)) :
    ∃C : ℝ,0<C ∧ ∀(rows : Finset FreeRow)(τ ψ : rows→Character)
      (N : rows→ℝ)(Q : rows→ℂ)(Y U : ℝ),
      0<Y → 1≤U → (∀i,0<N i ∧ N i≤b*Y) →
      (∀u∈rows,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤U) →
      (∀i,((ψ i).modulus.absNorm:ℝ)*
        (redundantIdeal (τ i).modulus (ψ i).modulus).absNorm≤Ccond*U) →
      (∀i,‖Q i‖≤Cslot*U^q) →
      (∑i:rows,‖discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/2))‖^4*‖Q i‖^2)≤C*U^(-saving) := by
  let s : ℝ := (1+2*q+saving)/4
  obtain ⟨C,hC,hbound⟩ := discardedSchwartz_fixed_profile xi s b Ccond hxi hb hCcond G
  refine ⟨128*C^4*Cslot^2,by positivity,?_⟩
  intro rows τ ψ N Q Y U hY hU hN hrows hcap hslot
  have hh := selected_tail_fourth Finset.univ
    (fun i:rows=>discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/2))) Q
    U 1 q s 128 C Cslot (zero_lt_one.trans_le hU) (by norm_num) hC.le hslot0.le
    (by simpa using ProbeHighRowFamily.freeRow_count rows U hU hrows)
    (fun i _=>hbound (τ i) (ψ i) Y (N i) U hY (hN i).1 (hN i).2 hU (hcap i))
    (fun i _=>hslot i)
  convert hh using 1
  dsimp only [s]
  congr 2
  ring

/-- Exact unit-modulus reflection transfers the retained weighted fourth moment
to the original polynomial, with a separately certified tail contribution. -/
theorem original_split_weighted_fourth {ι : Type*} (s : Finset ι)
    (P R T g Q : ι→ℂ) (D : ι→ℝ) (Er Et : ℝ)
    (hD : ∀i∈s,1≤D i) (hg : ∀i∈s,‖g i‖=1)
    (heq : ∀i∈s,P i=g i*(R i+T i))
    (hr : (∑i∈s,‖R i/(D i:ℂ)‖^4*‖Q i‖^2)≤Er)
    (ht : (∑i∈s,‖T i‖^4*‖Q i‖^2)≤Et) :
    (∑i∈s,‖P i/(D i:ℂ)‖^4*‖Q i‖^2)≤8*(Er+Et) := by
  have htail : (∑i∈s,‖T i/(D i:ℂ)‖^4*‖Q i‖^2)≤Et := by
    apply (Finset.sum_le_sum (fun i hi=>?_)).trans ht
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (hD i hi))]
    exact div_le_self (norm_nonneg _) (hD i hi)
  have hnorm (i : ι) (hi : i∈s) : ‖P i/(D i:ℂ)‖=‖R i/(D i:ℂ)+T i/(D i:ℂ)‖ := by
    rw [heq i hi,mul_div_assoc,norm_mul,hg i hi,one_mul,add_div]
  simp_rw [Finset.sum_congr rfl (fun i hi=>congrArg (fun t : ℝ=>t^4*‖Q i‖^2) (hnorm i hi))]
  exact weighted_fourth_add s (fun i=>R i/(D i:ℂ)) (fun i=>T i/(D i:ℂ)) Q Er Et hr htail

end Cycle25.Weighted.Numerator.PhysicalTail
end

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.Discarded -/
