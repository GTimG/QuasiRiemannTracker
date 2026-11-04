import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/- The proof terms below are checked by Lean. Python supplies explicit
   polynomial decompositions; their correctness is proved by ring. -/
set_option autoImplicit false
set_option maxHeartbeats 0
namespace BelowSevenEighthsTight
noncomputable section

def sigmaRat : ℝ := 8749570194201 / 10000000000000
def ellRat : ℝ := (1251289417397 / 7500000000000 : ℝ)
def bRat : ℝ := (61702842709770501 / 500000000000000000 : ℝ)
def kappaRat : ℝ := (3749570194201 / 5000000000000 : ℝ)
def cRat : ℝ := 1 / (3*kappaRat)
def hRat : ℝ := (1+3*ellRat+bRat)/2
def lyRat : ℝ := (1-ellRat+bRat)/2
def lxRat : ℝ := (1-ellRat-bRat)/2
def c0Rat : ℝ := -1/4+5*ellRat/4+bRat/6
def D (y : ℝ) : ℝ := 5/2-cRat+(1+2*cRat)*y
def P (y : ℝ) : ℝ := 1-cRat/2+2*y+2*cRat*y^2
def J (d y : ℝ) : ℝ := (5/6-d)*D y+d*P y
def countR (d y : ℝ) : ℝ := 1-d+(5/6-d)*d*P y/(2*J d y)
def endpointE (d y : ℝ) : ℝ :=
  c0Rat-(bRat/2+ellRat*y)*d+hRat*(5/6-d)*d*P y/(2*J d y)
def N (d y : ℝ) : ℝ :=
  J d y*(-2*c0Rat+(bRat+2*ellRat*y)*d)-hRat*(5/6-d)*d*P y
def certificatePolynomial (d y : ℝ) : ℝ := N d y - 2*J d y/1000000000000000

theorem rational_parameters :
    sigmaRat = 11/12-ellRat/4 ∧ kappaRat = 2*sigmaRat-1 ∧
    (13/18 : ℝ) < kappaRat ∧ kappaRat < 3/4 ∧
    (5/6 : ℝ) < sigmaRat ∧ sigmaRat < 7/8 ∧
    0 < hRat ∧ hRat+1/8000000000000000 < 1 := by
  norm_num [sigmaRat, ellRat, bRat, kappaRat, hRat]

theorem geometry_margins :
    0 < lxRat-ellRat ∧ 0 < lyRat-ellRat ∧
    0 < lyRat-ellRat-11*bRat/6 ∧ 0 < 5*ellRat-hRat ∧
    ellRat < 1/5 ∧ 0 < bRat ∧ 0 < 1-3*ellRat := by
  norm_num [lxRat, lyRat, ellRat, bRat, hRat]

theorem J_pos (d y : ℝ) (hd : 0 ≤ d) (hdu : d ≤ 5/6) (hy : 0 ≤ y) :
    0 < J d y := by
  have hc : 0 < cRat ∧ cRat < 1 := by norm_num [cRat, kappaRat]
  have hD : 1/2 ≤ D y := by dsimp [D]; nlinarith
  have hP : 1/2 ≤ P y := by
    dsimp [P]
    nlinarith [mul_nonneg hc.1.le (sq_nonneg y)]
  have h1 := mul_nonneg (sub_nonneg.mpr hdu) (sub_nonneg.mpr hD)
  have h2 := mul_nonneg hd (sub_nonneg.mpr hP)
  dsimp [J]
  nlinarith

theorem numerator_identity (d y : ℝ) (hj : J d y ≠ 0) :
    N d y = -2*J d y*endpointE d y := by
  unfold N endpointE
  field_simp
  <;> ring

theorem physical_endpoint_identity (d y : ℝ) :
    ((1+d)/2-sigmaRat+hRat*((17/50 : ℝ)-1/6)
      -(1+d)/2*lyRat-ellRat/2+d*(1/2-y)*ellRat
      +hRat*(countR d y+d/2-17/50)) = endpointE d y := by
  unfold endpointE countR c0Rat hRat lyRat sigmaRat ellRat bRat
  ring

private theorem box_0 (d y : ℝ)
    (hd : 0 ≤ d) (hdu : d ≤ (7 / 40 : ℝ))
    (hy : 0 ≤ y) (hyu : y ≤ (1 / 2 : ℝ)) :
    0 ≤ certificatePolynomial d y := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hy0 := sub_nonneg.mpr hy
  have hy1 := sub_nonneg.mpr hyu
  have heq : certificatePolynomial d y =
      (579454364316291295451923496897 / 31004258543299518750000000000 : ℝ)*((7 / 40 : ℝ)-d)^2*((1 / 2 : ℝ)-y)^3 +
      (626443700760086169701923496897 / 9688830794781099609375000000 : ℝ)*((7 / 40 : ℝ)-d)^2*(y-0)*((1 / 2 : ℝ)-y)^2 +
      (11354382959578387998682699447249 / 155021292716497593750000000000 : ℝ)*((7 / 40 : ℝ)-d)^2*(y-0)^2*((1 / 2 : ℝ)-y) +
      (62652448591726499 / 2296875000000000 : ℝ)*((7 / 40 : ℝ)-d)^2*(y-0)^3 +
      (318494874821772500040654181854119 / 15502129271649759375000000000000 : ℝ)*(d-0)*((7 / 40 : ℝ)-d)*((1 / 2 : ℝ)-y)^3 +
      (169205376972661103234341395896099 / 2583688211941626562500000000000 : ℝ)*(d-0)*((7 / 40 : ℝ)-d)*(y-0)*((1 / 2 : ℝ)-y)^2 +
      (1068047564395118109926989573690831 / 15502129271649759375000000000000 : ℝ)*(d-0)*((7 / 40 : ℝ)-d)*(y-0)^2*((1 / 2 : ℝ)-y) +
      (916920345507530307 / 38281250000000000 : ℝ)*(d-0)*((7 / 40 : ℝ)-d)*(y-0)^3 +
      (1750594896414956013043263572612957 / 310042585432995187500000000000000 : ℝ)*(d-0)^2*((1 / 2 : ℝ)-y)^3 +
      (2643171714838145555282811529464517 / 155021292716497593750000000000000 : ℝ)*(d-0)^2*(y-0)*((1 / 2 : ℝ)-y)^2 +
      (1906948311278961544859785105906399 / 103347528477665062500000000000000 : ℝ)*(d-0)^2*(y-0)^2*((1 / 2 : ℝ)-y) +
      (281151504732843657 / 38281250000000000 : ℝ)*(d-0)^2*(y-0)^3 := by
    unfold certificatePolynomial N J D P c0Rat hRat cRat kappaRat ellRat bRat
    ring
  rw [heq]
  positivity

private theorem box_1 (d y : ℝ)
    (hd : (7 / 40 : ℝ) ≤ d) (hdu : d ≤ (7 / 20 : ℝ))
    (hy : 0 ≤ y) (hyu : y ≤ (1 / 2 : ℝ)) :
    0 ≤ certificatePolynomial d y := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hy0 := sub_nonneg.mpr hy
  have hy1 := sub_nonneg.mpr hyu
  have heq : certificatePolynomial d y =
      (1750594896414956013043263572612957 / 310042585432995187500000000000000 : ℝ)*((7 / 20 : ℝ)-d)^2*((1 / 2 : ℝ)-y)^3 +
      (2643171714838145555282811529464517 / 155021292716497593750000000000000 : ℝ)*((7 / 20 : ℝ)-d)^2*(y-0)*((1 / 2 : ℝ)-y)^2 +
      (1906948311278961544859785105906399 / 103347528477665062500000000000000 : ℝ)*((7 / 20 : ℝ)-d)^2*(y-0)^2*((1 / 2 : ℝ)-y) +
      (281151504732843657 / 38281250000000000 : ℝ)*((7 / 20 : ℝ)-d)^2*(y-0)^3 +
      (79060261153046756419996331671181 / 38755323179124398437500000000000 : ℝ)*(d-(7 / 40 : ℝ))*((7 / 20 : ℝ)-d)*((1 / 2 : ℝ)-y)^3 +
      (13136382531028625845961323877879 / 4844415397390549804687500000000 : ℝ)*(d-(7 / 40 : ℝ))*((7 / 20 : ℝ)-d)*(y-0)*((1 / 2 : ℝ)-y)^2 +
      (190303555930647042472203724632521 / 38755323179124398437500000000000 : ℝ)*(d-(7 / 40 : ℝ))*((7 / 20 : ℝ)-d)*(y-0)^2*((1 / 2 : ℝ)-y) +
      (207685673423844321 / 38281250000000000 : ℝ)*(d-(7 / 40 : ℝ))*((7 / 20 : ℝ)-d)*(y-0)^3 +
      (14282058987959251266530496314267 / 77510646358248796875000000000000 : ℝ)*(d-(7 / 40 : ℝ))^2*((1 / 2 : ℝ)-y)^3 +
      (24261736232885712353421213389849 / 12918441059708132812500000000000 : ℝ)*(d-(7 / 40 : ℝ))^2*(y-0)*((1 / 2 : ℝ)-y)^2 +
      (717560769674897534650809304435387 / 77510646358248796875000000000000 : ℝ)*(d-(7 / 40 : ℝ))^2*(y-0)^2*((1 / 2 : ℝ)-y) +
      (62807400833454187 / 7177734375000000 : ℝ)*(d-(7 / 40 : ℝ))^2*(y-0)^3 := by
    unfold certificatePolynomial N J D P c0Rat hRat cRat kappaRat ellRat bRat
    ring
  rw [heq]
  positivity

private theorem box_2 (d y : ℝ)
    (hd : (9 / 20 : ℝ) ≤ d) (hdu : d ≤ (5 / 6 : ℝ))
    (hy : 0 ≤ y) (hyu : y ≤ (1 / 2 : ℝ)) :
    0 ≤ certificatePolynomial d y := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hy0 := sub_nonneg.mpr hy
  have hy1 := sub_nonneg.mpr hyu
  have heq : certificatePolynomial d y =
      (36187872280301610009460554232943 / 371910493637311687500000000000000 : ℝ)*((5 / 6 : ℝ)-d)^2*((1 / 2 : ℝ)-y)^3 +
      (23164349232288884627385809377331 / 14304249755281218750000000000000 : ℝ)*((5 / 6 : ℝ)-d)^2*(y-0)*((1 / 2 : ℝ)-y)^2 +
      (1897173876410473479459416721222383 / 371910493637311687500000000000000 : ℝ)*((5 / 6 : ℝ)-d)^2*(y-0)^2*((1 / 2 : ℝ)-y) +
      (1648100377787699253 / 413281250000000000 : ℝ)*((5 / 6 : ℝ)-d)^2*(y-0)^3 +
      (1343873159344058345803167210687 / 953616650352081250000000000000 : ℝ)*(d-(9 / 20 : ℝ))*((5 / 6 : ℝ)-d)*((1 / 2 : ℝ)-y)^3 +
      (52253020433701807875536502385649 / 4291274926584365625000000000000 : ℝ)*(d-(9 / 20 : ℝ))*((5 / 6 : ℝ)-d)*(y-0)*((1 / 2 : ℝ)-y)^2 +
      (3158447847559950971014994043602611 / 111573148091193506250000000000000 : ℝ)*(d-(9 / 20 : ℝ))*((5 / 6 : ℝ)-d)*(y-0)^2*((1 / 2 : ℝ)-y) +
      (15750149996181326081 / 826562500000000000 : ℝ)*(d-(9 / 20 : ℝ))*((5 / 6 : ℝ)-d)*(y-0)^3 +
      (3795357844999143847124512964309 / 743820987274623375000000000000 : ℝ)*(d-(9 / 20 : ℝ))^2*((1 / 2 : ℝ)-y)^3 +
      (14936276609590573437934636642927 / 557865740455967531250000000000 : ℝ)*(d-(9 / 20 : ℝ))^2*(y-0)*((1 / 2 : ℝ)-y)^2 +
      (20532205622719472093120173492927 / 446292592364774025000000000000 : ℝ)*(d-(9 / 20 : ℝ))^2*(y-0)^2*((1 / 2 : ℝ)-y) +
      (2552746749593916509 / 99187500000000000 : ℝ)*(d-(9 / 20 : ℝ))^2*(y-0)^3 := by
    unfold certificatePolynomial N J D P c0Rat hRat cRat kappaRat ellRat bRat
    ring
  rw [heq]
  positivity

private theorem box_3 (d y : ℝ)
    (hd : (7 / 20 : ℝ) ≤ d) (hdu : d ≤ (9 / 20 : ℝ))
    (hy : 0 ≤ y) (hyu : y ≤ (1 / 2 : ℝ)) :
    0 ≤ certificatePolynomial d y := by
  have hd0 := sub_nonneg.mpr hd
  have hd1 := sub_nonneg.mpr hdu
  have hy0 := sub_nonneg.mpr hy
  have hy1 := sub_nonneg.mpr hyu
  have heq : certificatePolynomial d y =
      (888315225353302318026768635299 / 1874785097100500000000000000000 : ℝ)*(d+(-12426642356881847400536634049661 / 31979348112718883448963670870764 : ℝ))^2 +
      (24217761725367607597241337062987850689800735945979 / 2158358589241717079733310729063519528558312152000000000000000000 : ℝ) +
      (34241413477812173440311930465431 / 33746131747809000000000000000000 : ℝ)*((9 / 20 : ℝ)-d)^2*y +
      (236903648230206681928498188760181 / 50619197621713500000000000000000 : ℝ)*(d-(7 / 20 : ℝ))*((9 / 20 : ℝ)-d)*y +
      (493709463198606170283649381111777 / 101238395243427000000000000000000 : ℝ)*(d-(7 / 20 : ℝ))^2*y +
      (360973932187805184776420179 / 38937844324395000000000000 : ℝ)*((9 / 20 : ℝ)-d)^2*y^2 +
      (6132454792446138499307946299 / 253095988108567500000000000 : ℝ)*(d-(7 / 20 : ℝ))*((9 / 20 : ℝ)-d)*y^2 +
      (890212592413729232070818107 / 56243552913015000000000000 : ℝ)*(d-(7 / 20 : ℝ))^2*y^2 +
      (122626362904906 / 33746131747809 : ℝ)*((9 / 20 : ℝ)-d)^2*y^3 +
      (35036103687116 / 3749570194201 : ℝ)*(d-(7 / 20 : ℝ))*((9 / 20 : ℝ)-d)*y^3 +
      (22523209513146 / 3749570194201 : ℝ)*(d-(7 / 20 : ℝ))^2*y^3 := by
    unfold certificatePolynomial N J D P c0Rat hRat cRat kappaRat ellRat bRat
    ring
  rw [heq]
  positivity

theorem certificate_nonneg (d y : ℝ) (hd : 0 ≤ d) (hdu : d ≤ 5/6)
    (hy : 0 ≤ y) (hyu : y ≤ 1/2) : 0 ≤ certificatePolynomial d y := by
  by_cases hc0 : d ≤ (7 / 40 : ℝ)
  · exact box_0 d y (by linarith) (by linarith) (by linarith) (by linarith)
  · by_cases hc1 : d ≤ (7 / 20 : ℝ)
    · exact box_1 d y (by linarith) (by linarith) (by linarith) (by linarith)
    · by_cases hc2 : d ≤ (9 / 20 : ℝ)
      · exact box_3 d y (by linarith) (by linarith) (by linarith) (by linarith)
      · exact box_2 d y (by linarith) (by linarith) (by linarith) (by linarith)

theorem rational_endpoint_bound (d y : ℝ) (hd : 0 ≤ d) (hdu : d ≤ 5/6)
    (hy : 0 ≤ y) (hyu : y ≤ 1/2) : endpointE d y ≤ -1/1000000000000000 := by
  have hj := J_pos d y hd hdu hy
  have hn := certificate_nonneg d y hd hdu hy hyu
  unfold certificatePolynomial at hn
  rw [numerator_identity d y (ne_of_gt hj)] at hn
  nlinarith

#print axioms rational_endpoint_bound
#print axioms physical_endpoint_identity
end
end BelowSevenEighthsTight
