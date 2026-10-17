import Candidate.Cycle63.Arithmetic.Bernstein.Basis
import Candidate.Target836.Detector836.Arith
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
