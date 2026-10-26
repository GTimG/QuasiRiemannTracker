import Candidate.Cycle63.Arithmetic.Bernstein.Basis
import Candidate.Target836.Detector836.Arith
import Candidate.Affine.Balanced

/- Original module: Candidate.Target836.Detector836.Positive. -/
section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Detector836.Positive
noncomputable section
open Cycle63.Arithmetic.Bernstein

def regionCrossLoPower (δ p : ℝ) : ℝ := (-11142040000/14495225413)*δ^1*p^3 +
  (4218553755627/1449522541300)*δ^1*p^2 +
  (-284216717/73234100)*δ^1*p^1 +
  (69/37)*δ^1*p^0 +
  (254535407191/579809016520)*δ^0*p^2 +
  (-77464883/87880920)*δ^0*p^1 +
  (25/74)*δ^0*p^0
def regionCrossLoMinimum : ℝ := 896001016418369/3478854099120000
theorem regionCrossLoMinimum_pos : 0 < regionCrossLoMinimum := by norm_num [regionCrossLoMinimum]
def regionCrossLoCoefficients0 : Fin 3 → Fin 4 → ℝ := ![
  ![(11701221152039504531/43485676239000000000 : ℝ), (34597069417181085731/130457028717000000000 : ℝ), (340958760455513137/1304570287170000000 : ℝ), (896001016418369/3478854099120000 : ℝ)],
  ![(24371737817098371721/86971352478000000000 : ℝ), (72075186978119140921/260914057434000000000 : ℝ), (710462637784019267/2609140574340000000 : ℝ), (1867422653072179/6957708198240000 : ℝ)],
  ![(1267051666505886719/4348567623900000000 : ℝ), (3747811756093805519/13045702871700000000 : ℝ), (36950387732850613/130457028717000000 : ℝ), (97142163665381/347885409912000 : ℝ)]]
theorem regionCrossLoCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionCrossLoMinimum ≤ regionCrossLoCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionCrossLoMinimum,regionCrossLoCoefficients0]
theorem regionCrossLoIdentity0 (δ p : ℝ) :
    regionCrossLoPower δ p = tensor regionCrossLoCoefficients0
      ((δ-451/1000)/(49/100-451/1000)) ((p-49/100)/(1/2-49/100)) := by
  norm_num [regionCrossLoPower,tensor,basis2,basis3,regionCrossLoCoefficients0,Fin.sum_univ_succ]
  ring
theorem regionCrossLoBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000) (49/100)) (hp : p ∈ Set.Icc (49/100) (1/2)) :
    0 < regionCrossLoPower δ p := by
  rw [regionCrossLoIdentity0]
  exact tensor_pos regionCrossLoMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionCrossLoCoefficients0_lower

def regionCrossHiPower (δ p : ℝ) : ℝ := (-39277561271/39176284900)*δ^1*p^2 +
  (6940441/1979300)*δ^1*p^1 +
  (-3)*δ^1*p^0 +
  (39277561271/47011541880)*δ^0*p^2 +
  (-6940441/2375160)*δ^0*p^1 +
  (5/2)*δ^0*p^0
def regionCrossHiMinimum : ℝ := 4833762862487/9402308376000
theorem regionCrossHiMinimum_pos : 0 < regionCrossHiMinimum := by norm_num [regionCrossHiMinimum]
def regionCrossHiCoefficients0 : Fin 3 → Fin 4 → ℝ := ![
  ![(228050532675637579/391762849000000000 : ℝ), (2041113242175585137/3525865641000000000 : ℝ), (2255351935148011/3917628490000000 : ℝ), (53828407798763/94023083760000 : ℝ)],
  ![(432838718077474289/783525698000000000 : ℝ), (3874022256509371267/7051731282000000000 : ℝ), (4280646175080401/7835256980000000 : ℝ), (102166036423633/188046167520000 : ℝ)],
  ![(20478818540183671/39176284900000000 : ℝ), (183290901433378613/352586564100000000 : ℝ), (202529423993239/391762849000000 : ℝ), (4833762862487/9402308376000 : ℝ)]]
theorem regionCrossHiCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionCrossHiMinimum ≤ regionCrossHiCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionCrossHiMinimum,regionCrossHiCoefficients0]
theorem regionCrossHiIdentity0 (δ p : ℝ) :
    regionCrossHiPower δ p = tensor regionCrossHiCoefficients0
      ((δ-451/1000)/(49/100-451/1000)) ((p-49/100)/(1/2-49/100)) := by
  norm_num [regionCrossHiPower,tensor,basis2,basis3,regionCrossHiCoefficients0,Fin.sum_univ_succ]
  ring
theorem regionCrossHiBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000) (49/100)) (hp : p ∈ Set.Icc (49/100) (1/2)) :
    0 < regionCrossHiPower δ p := by
  rw [regionCrossHiIdentity0]
  exact tensor_pos regionCrossHiMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionCrossHiCoefficients0_lower

def regionPlainPower (δ p : ℝ) : ℝ := (-1575046733/9794071225)*δ^1*p^3 +
  (56108065661/39586000000)*δ^1*p^2 +
  (-51263315661/19793000000)*δ^1*p^1 +
  (2486169/2000000)*δ^1*p^0 +
  (-526717431651827/940230837600000)*δ^0*p^2 +
  (29527713017/23751600000)*δ^0*p^1 +
  (-486169/800000)*δ^0*p^0
def regionPlainMinimum : ℝ := 1312748516156329723/7835256980000000000000
theorem regionPlainMinimum_pos : 0 < regionPlainMinimum := by norm_num [regionPlainMinimum]
def regionPlainCoefficients0 : Fin 3 → Fin 4 → ℝ := ![
  ![(1312748516156329723/7835256980000000000000 : ℝ), (35396353770544571869/70517312820000000000000 : ℝ), (16364760343184179/19588142450000000000 : ℝ), (2196265934624293/1880461675200000000 : ℝ)],
  ![(92889065406280649993/15670513960000000000000 : ℝ), (871093533914066455679/141034625640000000000000 : ℝ), (251712242905712389/39176284900000000000 : ℝ), (25098734374383863/3760923350400000000 : ℝ)],
  ![(9157631689012432027/783525698000000000000 : ℝ), (83569718014352188381/7051731282000000000000 : ℝ), (23534748256252821/1958814245000000000 : ℝ), (2290246843975957/188046167520000000 : ℝ)]]
theorem regionPlainCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionPlainMinimum ≤ regionPlainCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionPlainMinimum,regionPlainCoefficients0]
theorem regionPlainIdentity0 (δ p : ℝ) :
    regionPlainPower δ p = tensor regionPlainCoefficients0
      ((δ-451/1000)/(49/100-451/1000)) ((p-49/100)/(1/2-49/100)) := by
  norm_num [regionPlainPower,tensor,basis2,basis3,regionPlainCoefficients0,Fin.sum_univ_succ]
  ring
theorem regionPlainBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000) (49/100)) (hp : p ∈ Set.Icc (49/100) (1/2)) :
    0 < regionPlainPower δ p := by
  rw [regionPlainIdentity0]
  exact tensor_pos regionPlainMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionPlainCoefficients0_lower

def regionTailPower (δ p : ℝ) : ℝ := (1360/19793)*δ^1*p^3 +
  (-7138197/9896500)*δ^1*p^2 +
  (250767/158344)*δ^1*p^1 +
  (-847/1000)*δ^1*p^0 +
  (1194091/3958600)*δ^0*p^2 +
  (-19537369/23751600)*δ^0*p^1 +
  (541/1200)*δ^0*p^0
def regionTailMinimum : ℝ := 3743991/989650000
theorem regionTailMinimum_pos : 0 < regionTailMinimum := by norm_num [regionTailMinimum]
def regionTailCoefficients0 : Fin 3 → Fin 4 → ℝ := ![
  ![(4073852066909/296895000000000 : ℝ), (11897378792659/890685000000000 : ℝ), (231477030907/17813700000000 : ℝ), (62505567/4948250000 : ℝ)],
  ![(5414027325319/593790000000000 : ℝ), (15700984668569/1781370000000000 : ℝ), (303209389337/35627400000000 : ℝ), (40612761/4948250000 : ℝ)],
  ![(134017525841/29689500000000 : ℝ), (380360587591/89068500000000 : ℝ), (7173235843/1781370000000 : ℝ), (3743991/989650000 : ℝ)]]
theorem regionTailCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionTailMinimum ≤ regionTailCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionTailMinimum,regionTailCoefficients0]
theorem regionTailIdentity0 (δ p : ℝ) :
    regionTailPower δ p = tensor regionTailCoefficients0
      ((δ-451/1000)/(49/100-451/1000)) ((p-49/100)/(1/2-49/100)) := by
  norm_num [regionTailPower,tensor,basis2,basis3,regionTailCoefficients0,Fin.sum_univ_succ]
  ring
theorem regionTailBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000) (49/100)) (hp : p ∈ Set.Icc (49/100) (1/2)) :
    0 < regionTailPower δ p := by
  rw [regionTailIdentity0]
  exact tensor_pos regionTailMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionTailCoefficients0_lower

def regionCutoffPower (δ p : ℝ) : ℝ := (12953/1979300)*δ^1*p^2 +
  (1976697/1979300)*δ^1*p^1 +
  (-3/2)*δ^1*p^0 +
  (-198965/237516)*δ^0*p^1 +
  (5/4)*δ^0*p^0
def regionCutoffMinimum : ℝ := 811435409/2375160000
theorem regionCutoffMinimum_pos : 0 < regionCutoffMinimum := by norm_num [regionCutoffMinimum]
def regionCutoffCoefficients0 : Fin 3 → Fin 4 → ℝ := ![
  ![(22827630607909/59379000000000 : ℝ), (68254643917909/178137000000000 : ℝ), (5442113083/14250960000 : ℝ), (9039760091/23751600000 : ℝ)],
  ![(43318468823819/118758000000000 : ℝ), (129522186533819/356274000000000 : ℝ), (10327120253/28501920000 : ℝ), (17154114181/47503200000 : ℝ)],
  ![(2049083821591/5937900000000 : ℝ), (6126754261591/17813700000000 : ℝ), (488500717/1425096000 : ℝ), (811435409/2375160000 : ℝ)]]
theorem regionCutoffCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    regionCutoffMinimum ≤ regionCutoffCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionCutoffMinimum,regionCutoffCoefficients0]
theorem regionCutoffIdentity0 (δ p : ℝ) :
    regionCutoffPower δ p = tensor regionCutoffCoefficients0
      ((δ-451/1000)/(49/100-451/1000)) ((p-49/100)/(1/2-49/100)) := by
  norm_num [regionCutoffPower,tensor,basis2,basis3,regionCutoffCoefficients0,Fin.sum_univ_succ]
  ring
theorem regionCutoffBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000) (49/100)) (hp : p ∈ Set.Icc (49/100) (1/2)) :
    0 < regionCutoffPower δ p := by
  rw [regionCutoffIdentity0]
  exact tensor_pos regionCutoffMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionCutoffCoefficients0_lower

def regionComparePower (δ p : ℝ) : ℝ := (12953/494825)*δ^1*p^4 +
  (-40594188031/123706250000)*δ^1*p^3 +
  (269716/494825)*δ^1*p^2 +
  (-30073061969/123706250000)*δ^1*p^1 +
  (8944937323/49482500000)*δ^0*p^3 +
  (-12406249469/37111875000)*δ^0*p^2 +
  (22790185907/148447500000)*δ^0*p^1
def regionCompareMinimum : ℝ := 1098221257921/296895000000000
theorem regionCompareMinimum_pos : 0 < regionCompareMinimum := by norm_num [regionCompareMinimum]
def regionCompareCoefficients0 : Fin 3 → Fin 5 → ℝ := ![
  ![(593751639523002331/123706250000000000000 : ℝ), (7074370659182628043/1484475000000000000000 : ℝ), (210694370254338221/44534250000000000000 : ℝ), (2788546189082357/593790000000000000 : ℝ), (13838101955329/2968950000000000 : ℝ)],
  ![(1065227186506626521/247412500000000000000 : ℝ), (12691128996003165113/2968950000000000000000 : ℝ), (377954300893698511/89068500000000000000 : ℝ), (5001922733441287/1187580000000000000 : ℝ), (24820314534539/5937900000000000 : ℝ)],
  ![(47147554698362419/12370625000000000000 : ℝ), (561675833682053707/148447500000000000000 : ℝ), (16725993063936029/4453425000000000000 : ℝ), (221337654435893/59379000000000000 : ℝ), (1098221257921/296895000000000 : ℝ)]]
theorem regionCompareCoefficients0_lower (i : Fin 3) (j : Fin 5) :
    regionCompareMinimum ≤ regionCompareCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [regionCompareMinimum,regionCompareCoefficients0]
theorem regionCompareIdentity0 (δ p : ℝ) :
    regionComparePower δ p = tensor24 regionCompareCoefficients0
      ((δ-451/1000)/(49/100-451/1000)) ((p-49/100)/(1/2-49/100)) := by
  norm_num [regionComparePower,tensor24,basis2,basis4,regionCompareCoefficients0,Fin.sum_univ_succ]
  ring
theorem regionCompareBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (451/1000) (49/100)) (hp : p ∈ Set.Icc (49/100) (1/2)) :
    0 < regionComparePower δ p := by
  rw [regionCompareIdentity0]
  exact tensor24_pos regionCompareMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    regionCompareCoefficients0_lower
end
end Detector836.Positive
#print axioms Detector836.Positive.regionPlainBox0_pos
#print axioms Detector836.Positive.regionCompareBox0_pos
end

/- Original module: Candidate.Target836.Detector836.Region. -/
section
/- Copyright (c) 2026. Released under Apache 2.0. -/

/-! Consequences of the region certificates: the new cutoff is admissible,
the crossing lies in the inverse range, the affine window contains the
crossing plain length, the old plain tail is dominated, the new count is
below the old count at `kappaStar`, and the new row closes at `theta`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Detector836
noncomputable section
open Detector836.Positive

/-- `kappaStar = 2*theta-1` at theta = 21871/25000. -/
def kStar : ℝ := 93709/125000
/-- The old count numerator/denominator at `kStar` (`countingCoefficient`). -/
def oldNum (p : ℝ) : ℝ := 2*(1-p)*(3*kStar-p)
def oldDen (p : ℝ) : ℝ := 3*kStar*(3-p)-2*p
/-- The old detector count at `kStar` (`countingR kappaStar`). -/
def ROld (δ p : ℝ) : ℝ :=
  1-δ+δ*(oldNum p/oldDen p)*(5/6-δ)/(2*((5/6-δ)+δ*(oldNum p/oldDen p)))

theorem region_box {δ p : ℝ} (h : InRegion δ p) :
    δ ∈ Set.Icc (451/1000:ℝ) (49/100) ∧ p ∈ Set.Icc (49/100:ℝ) (1/2) :=
  ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩

theorem regionCrossLo_binding (δ p : ℝ) : regionCrossLoPower δ p =
    aN p*numT δ p+(2*p*Bc/lam-p)*JN δ p-23/37*DN p*JN δ p := by
  unfold regionCrossLoPower numT JN DN aN cN lam Bc
  ring

theorem regionCrossHi_binding (δ p : ℝ) : regionCrossHiPower δ p =
    DN p*JN δ p-(aN p*numT δ p+(2*p*Bc/lam-p)*JN δ p) := by
  unfold regionCrossHiPower numT JN DN aN cN lam Bc
  ring

theorem regionPlain_binding (δ p : ℝ) : regionPlainPower δ p =
    (1-p)*numT δ p+(p-2*p*Bc/lam)*JN δ p-(mLo+1/100000)*DN p*JN δ p := by
  unfold regionPlainPower numT JN DN aN cN mLo lam Bc
  ring

theorem regionTail_binding (δ p : ℝ) : regionTailPower δ p =
    JN δ p*(-1+2*mHi+2*p*(1-2*mHi)/(6*(3/4)))+(5/6-δ)*(1-p)*cN p := by
  unfold regionTailPower JN DN aN cN mHi lam Bc
  ring

theorem regionCutoff_binding (δ p : ℝ) : regionCutoffPower δ p =
    3/2*JN δ p-numT δ p := by
  unfold regionCutoffPower numT JN DN aN cN lam Bc
  ring

theorem regionCompare_binding (δ p : ℝ) : regionComparePower δ p =
    oldNum p*JN δ p-2*(1-p)*cN p*((5/6-δ)*oldDen p+δ*oldNum p) := by
  unfold regionComparePower oldNum oldDen kStar JN DN aN cN lam Bc
  ring

theorem region_p {δ p : ℝ} (h : InRegion δ p) : 0 ≤ p ∧ p ≤ 1/2 :=
  ⟨by linarith [h.2.2.1], h.2.2.2⟩

theorem region_DN_pos {δ p : ℝ} (h : InRegion δ p) : 0 < DN p :=
  DN_pos (region_p h).1 (region_p h).2

theorem region_JN_pos {δ p : ℝ} (h : InRegion δ p) : 0 < JN δ p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hV : 0 < 5/6-δ := by linarith
  have hD := DN_pos (p:=p) (by linarith) h4
  have hA := aN_pos (p:=p) (by linarith) h4
  unfold JN
  have : 0 ≤ δ*(1-p)*aN p := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hA.le
  have := mul_pos hV hD
  linarith

theorem region_tN_mul {δ p : ℝ} (h : InRegion δ p) : tN δ p*JN δ p = numT δ p :=
  div_mul_cancel₀ _ (region_JN_pos h).ne'

theorem region_tN {δ p : ℝ} (h : InRegion δ p) : 1 ≤ tN δ p ∧ tN δ p ≤ 3/2 := by
  have hJ := region_JN_pos h
  have hT := region_tN_mul h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc := cN_pos (p:=p) (by linarith) h4
  have hnum : JN δ p ≤ numT δ p := by
    unfold numT JN
    have : 0 ≤ δ*(1-p)*cN p := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hc.le
    nlinarith
  have hcut := regionCutoffBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionCutoff_binding] at hcut
  constructor
  · by_contra hlt
    have := mul_lt_mul_of_pos_right (lt_of_not_ge hlt) hJ
    linarith
  · by_contra hlt
    have := mul_lt_mul_of_pos_right (lt_of_not_ge hlt) hJ
    linarith

theorem region_rN_mul {δ p : ℝ} (h : InRegion δ p) :
    rN p (tN δ p)*DN p = aN p*tN δ p+2*p*Bc/lam-p :=
  div_mul_cancel₀ _ (region_DN_pos h).ne'

theorem region_rN {δ p : ℝ} (h : InRegion δ p) :
    23/37 ≤ rN p (tN δ p) ∧ rN p (tN δ p) ≤ 1 := by
  have hJ := region_JN_pos h
  have hD := region_DN_pos h
  have hT := region_tN_mul h
  have hr := region_rN_mul h
  have hDJ := mul_pos hD hJ
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlo := regionCrossLoBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  have hhi := regionCrossHiBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionCrossLo_binding] at hlo
  rw [regionCrossHi_binding] at hhi
  have klo : (rN p (tN δ p)-23/37)*(DN p*JN δ p) =
      aN p*numT δ p+(2*p*Bc/lam-p)*JN δ p-23/37*DN p*JN δ p := by
    linear_combination (JN δ p)*hr+(aN p)*hT
  have khi : (1-rN p (tN δ p))*(DN p*JN δ p) =
      DN p*JN δ p-(aN p*numT δ p+(2*p*Bc/lam-p)*JN δ p) := by
    linear_combination (-(JN δ p))*hr-(aN p)*hT
  constructor
  · have := (mul_pos_iff_of_pos_right hDJ).mp (klo ▸ hlo)
    linarith
  · have := (mul_pos_iff_of_pos_right hDJ).mp (khi ▸ hhi)
    linarith

theorem region_mN {δ p : ℝ} (h : InRegion δ p) :
    mLo+1/100000 ≤ tN δ p-rN p (tN δ p) := by
  have hJ := region_JN_pos h
  have hD := region_DN_pos h
  have hT := region_tN_mul h
  have hr := region_rN_mul h
  have hDJ := mul_pos hD hJ
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hpl := regionPlainBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionPlain_binding] at hpl
  have k : (tN δ p-rN p (tN δ p)-(mLo+1/100000))*(DN p*JN δ p) =
      (1-p)*numT δ p+(p-2*p*Bc/lam)*JN δ p-(mLo+1/100000)*DN p*JN δ p := by
    have hDa : DN p-aN p = 1-p := by unfold DN aN; ring
    linear_combination (DN p-aN p)*hT-(JN δ p)*hr+(numT δ p)*hDa
  have := (mul_pos_iff_of_pos_right hDJ).mp (k ▸ hpl)
  linarith

theorem region_short {δ p : ℝ} (h : InRegion δ p) :
    shortNew δ p (tN δ p) = RNew δ p :=
  short_at_tN (region_JN_pos h).ne' (region_DN_pos h).ne'

theorem region_max {δ p : ℝ} (h : InRegion δ p) :
    max (shortNew δ p (tN δ p)) (longExp δ (tN δ p)) = RNew δ p :=
  max_at_tN (region_JN_pos h).ne' (region_DN_pos h).ne'

theorem region_RNew_mul {δ p : ℝ} (h : InRegion δ p) :
    (RNew δ p-1+δ)*JN δ p = (5/6-δ)*δ*(1-p)*cN p := by
  unfold RNew
  rw [show 1-δ+(5/6-δ)*δ*(1-p)*cN p/JN δ p-1+δ = (5/6-δ)*δ*(1-p)*cN p/JN δ p by ring]
  exact div_mul_cancel₀ _ (region_JN_pos h).ne'

/-- The old κ-plain tail above `mHi` is dominated by the new short exponent. -/
theorem region_tail {δ p κ : ℝ} (h : InRegion δ p) (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4) :
    oldPlainExp δ p κ mHi ≤ shortNew δ p (tN δ p) := by
  rw [region_short h]
  have hJ := region_JN_pos h
  have hR := region_RNew_mul h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ht := regionTailBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionTail_binding] at ht
  have hk0 : 0 < 6*κ := by linarith
  -- 1/(6κ) ≥ 1/(6*(3/4))
  have hinv : 2*p*(1-2*mHi)/(6*(3/4)) ≤ 2*p*(1-2*mHi)/(6*κ) := by
    apply div_le_div_of_nonneg_left _ hk0 (by linarith)
    unfold mHi; nlinarith
  have hdiff : (RNew δ p-oldPlainExp δ p κ mHi)*JN δ p ≥
      δ*(JN δ p*(-1+2*mHi+2*p*(1-2*mHi)/(6*(3/4)))+(5/6-δ)*(1-p)*cN p) := by
    have e : (RNew δ p-oldPlainExp δ p κ mHi)*JN δ p =
        (RNew δ p-1+δ)*JN δ p+δ*JN δ p*(-1+2*mHi+2*p*(1-2*mHi)/(6*κ)) := by
      unfold oldPlainExp; field_simp; ring
    rw [e, hR]
    have := mul_le_mul_of_nonneg_left hinv (mul_nonneg (by linarith : (0:ℝ) ≤ δ) hJ.le)
    nlinarith
  have hpos : 0 ≤ (RNew δ p-oldPlainExp δ p κ mHi)*JN δ p := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ δ) ht.le
    linarith
  have := nonneg_of_mul_nonneg_left hpos hJ
  linarith

theorem oldDen_pos {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 < oldDen p := by
  unfold oldDen kStar; nlinarith

theorem oldNum_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1/2) : 0 ≤ oldNum p := by
  unfold oldNum kStar
  apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)

/-- The new count is at most the old count at `kStar` on the region. -/
theorem region_compare {δ p : ℝ} (h : InRegion δ p) : RNew δ p ≤ ROld δ p := by
  have hJ := region_JN_pos h
  have hR := region_RNew_mul h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc := regionCompareBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [regionCompare_binding] at hc
  have hD := oldDen_pos (p:=p) (by linarith) h4
  have hN := oldNum_nonneg (p:=p) (by linarith) h4
  have hcN := cN_pos (p:=p) (by linarith) h4
  set c := oldNum p/oldDen p with hcdef
  have hc0 : 0 ≤ c := div_nonneg hN hD.le
  have hcD : c*oldDen p = oldNum p := div_mul_cancel₀ _ hD.ne'
  have hV : 0 < 5/6-δ := by linarith
  have hS : 0 < (5/6-δ)+δ*c := by nlinarith
  -- RNew - (1-δ) = Vδ(1-p)cN/JN ≤ δ c V/(2 S)
  have hlhs : RNew δ p-(1-δ) = (5/6-δ)*δ*(1-p)*cN p/JN δ p := by unfold RNew; ring
  have hrhs : ROld δ p-(1-δ) = δ*c*(5/6-δ)/(2*((5/6-δ)+δ*c)) := by unfold ROld; ring
  have key : (5/6-δ)*δ*(1-p)*cN p/JN δ p ≤ δ*c*(5/6-δ)/(2*((5/6-δ)+δ*c)) := by
    rw [div_le_div_iff₀ hJ (by positivity)]
    -- cross-multiplied: Vδ(1-p)cN * 2S ≤ δ c V JN; divide by Vδ ≥ 0 and use certificate
    have hcert : 2*(1-p)*cN p*((5/6-δ)+δ*c) ≤ c*JN δ p := by
      have e1 : (c*JN δ p-2*(1-p)*cN p*((5/6-δ)+δ*c))*oldDen p =
          oldNum p*JN δ p-2*(1-p)*cN p*((5/6-δ)*oldDen p+δ*oldNum p) := by
        linear_combination (JN δ p-2*(1-p)*cN p*δ)*hcD
      have := (mul_pos_iff_of_pos_right hD).mp (e1 ▸ hc)
      linarith
    have hVδ : 0 ≤ (5/6-δ)*δ := mul_nonneg hV.le (by linarith)
    have := mul_le_mul_of_nonneg_left hcert hVδ
    nlinarith
  linarith

end
end Detector836

#print axioms Detector836.region_tN
#print axioms Detector836.region_rN
#print axioms Detector836.region_mN
#print axioms Detector836.region_tail
#print axioms Detector836.region_compare
end

/- Original module: Candidate.Target836.Detector836.Schedule. -/
section

set_option autoImplicit false
namespace Detector836
noncomputable section

def InAcceptedRegion (δ p : ℝ) : Prop :=
  89/200 ≤ δ ∧ δ ≤ 451/1000 ∧ 199/400 ≤ p ∧ p ≤ 1/2
instance (δ p : ℝ) : Decidable (InAcceptedRegion δ p) := Classical.dec _

theorem accepted_region_subset {δ p : ℝ} (h : InAcceptedRegion δ p) :
    DetectorAffine.InRegion δ p := by
  rcases h with ⟨h1,h2,h3,h4⟩
  exact ⟨h1,by linarith,h3,h4⟩

def count (κ δ p : ℝ) : ℝ :=
  if InRegion δ p ∧ kStar ≤ κ then RNew δ p else
  if InAcceptedRegion δ p ∧ kStar ≤ κ then DetectorAffine.RNew δ p else
  Cycle63.Arithmetic.Bernstein.countingR0 κ δ p

def cutoff (δ p κ : ℝ) : ℝ :=
  if InRegion δ p ∧ kStar ≤ κ then tN δ p else
  if InAcceptedRegion δ p ∧ kStar ≤ κ then DetectorAffine.tN δ p else
  OAI.SevenEighths.Cycle25DetectorRowCount.cutoff δ p κ

theorem cutoff_bounds {δ p κ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 3/4)
    (hp : 0 ≤ p) (hp1 : p ≤ 1/2) (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4) :
    1 ≤ cutoff δ p κ ∧ cutoff δ p κ ≤ 3/2 := by
  unfold cutoff
  split_ifs with hn ha
  · exact region_tN hn.1
  · exact DetectorAffine.region_tN (accepted_region_subset ha.1)
  · exact OAI.SevenEighths.Cycle25DetectorRowCount.cutoff_bounds hδ hδ1 hp hp1 hk hk1

theorem count_gap {a κ δ p : ℝ} (ha : kStar ≤ a) (hak : a ≤ κ)
    (hδ : 0 ≤ δ ∧ δ ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    count κ δ p-count a δ p ≤ (5/12)*((κ-a)/18) := by
  by_cases hn : InRegion δ p
  · simp only [count,hn,ha,ha.trans hak,and_self,ite_true,sub_self]
    have hgap : 0 ≤ κ-a := sub_nonneg.mpr hak
    linarith
  · by_cases hb : InAcceptedRegion δ p
    · simp only [count,hn,hb,ha,ha.trans hak,false_and,and_self,ite_true,ite_false,sub_self]
      have hgap : 0 ≤ κ-a := sub_nonneg.mpr hak
      linarith
    · simp only [count,hn,hb,false_and,ite_false]
      apply Cycle63.Arithmetic.Bernstein.row_gap _ hak hδ hp
      have : (7/10:ℝ) ≤ kStar := by norm_num [kStar]
      exact this.trans ha

end
end Detector836

#print axioms Detector836.cutoff_bounds
#print axioms Detector836.count_gap
end
