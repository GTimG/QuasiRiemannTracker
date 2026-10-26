import Mathlib

/- Original module: Candidate.Uneven.Endpoint. -/
section

/- Copyright (c) 2026 Sil. Apache-2.0.
   Prepared with OpenAI Codex assistance.
   This file proves the algebraic endpoint and rounding, not L-function nonvanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Sil.Uneven
noncomputable section

def quadA : ℝ := 6093050555534740855143533085201471
def quadB : ℝ := 11216192073911255069710427525384691
def quadC : ℝ := 5149081167263611203406370372027234
def discriminant : ℝ := quadB ^ 2 - 4 * quadA * quadC
def endpoint : ℝ := (quadB - Real.sqrt discriminant) / (2 * quadA)
def submittedBound : ℝ := 874828524351 / 1000000000000
def lower : ℝ := 8748285243509452822184826547948 / 10000000000000000000000000000000
def upper : ℝ := 8748285243509452822184826547950 / 10000000000000000000000000000000

theorem quadA_pos : 0 < quadA := by norm_num [quadA]
theorem discriminant_pos : 0 < discriminant := by
  norm_num [discriminant, quadA, quadB, quadC]

theorem endpoint_polynomial :
    quadA * endpoint ^ 2 - quadB * endpoint + quadC = 0 := by
  have hs := Real.sq_sqrt (le_of_lt discriminant_pos)
  have ha : quadA ≠ 0 := ne_of_gt quadA_pos
  dsimp only [endpoint]
  field_simp
  change Real.sqrt discriminant ^ 2 = quadB ^ 2 - 4 * quadA * quadC at hs
  nlinarith only [hs]

theorem endpoint_isolation : lower < endpoint ∧ endpoint < upper := by
  have hs := Real.sq_sqrt (le_of_lt discriminant_pos)
  have hn := Real.sqrt_nonneg discriminant
  have hlowpos : 0 < quadB - 2 * quadA * lower := by
    norm_num [quadB, quadA, lower]
  have huppos : 0 < quadB - 2 * quadA * upper := by
    norm_num [quadB, quadA, upper]
  have hlow : discriminant < (quadB - 2 * quadA * lower)^2 := by
    norm_num [discriminant, quadA, quadB, quadC, lower]
  have hupp : (quadB - 2 * quadA * upper)^2 < discriminant := by
    norm_num [discriminant, quadA, quadB, quadC, upper]
  have hslo : Real.sqrt discriminant < quadB - 2 * quadA * lower := by
    nlinarith only [hs, hn, hlowpos, hlow]
  have hshi : quadB - 2 * quadA * upper < Real.sqrt discriminant := by
    nlinarith only [hs, hn, huppos, hupp]
  constructor
  · unfold endpoint
    rw [lt_div_iff₀ (by exact mul_pos (by norm_num) quadA_pos : 0 < 2 * quadA)]
    linarith only [hslo]
  · unfold endpoint
    rw [div_lt_iff₀ (by exact mul_pos (by norm_num) quadA_pos : 0 < 2 * quadA)]
    linarith only [hshi]

theorem endpoint_lt_submitted : endpoint < submittedBound := by
  have h := endpoint_isolation.2
  have hu : upper < submittedBound := by norm_num [upper, submittedBound]
  exact h.trans hu




end
end Sil.Uneven
end

/- Original module: Candidate.Uneven.CriticalHalf. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   This file is only the critical-row algebra; it is not an analytic source proof. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Sil.Uneven.Critical
noncomputable section

def parameterPolynomial (v : ℝ) : ℝ := (68829760479687653132500 + (-191011230531473313491625 * v) + (91804891419376373332989 * (v ^ 2)))

def criticalTheta (v : ℝ) : ℝ := ((1/677005617281637872793725898355719:ℝ) * (567450664717496215205934736498337 + (53513930593943064798030058210029 * v)))

def criticalHeight (v : ℝ) : ℝ := ((6994912332/49968722309439657004318790966985043884232644046099976816135970525060125549:ℝ) * (7557749495571114292507544377461412922157493616026381864542400775 + (-4019635498657897742511108248017721263274119229323182364458666606 * v)))

def halfDenominator (d : ℝ) : ℝ := ((1/222692807916:ℝ) * (363943349825 + (-274039211874 * d)))

def halfNumerator (d : ℝ) : ℝ := ((1/4453856158320:ℝ) * (7278866996500 + (-11393134690085 * d) + (3840964384806 * (d ^ 2))))

def squareCoefficient (v : ℝ) : ℝ := ((582909361/30910208552955526252376912497889322987100696504485953294577280370765145008984169571900:ℝ) * (7523203541522138545083732423005053576604149679946576882719597385241377646775 + (5909712235488191390397393563708703934495592639548882228890480482347153986306 * v)))

def physicalB : ℝ := 49061544613/50000000000
def physicalLambda : ℝ := 1891221821/500000000
def countB : ℝ := 97851371081/100000000000
def countLambda : ℝ := 18557733993/5000000000

def countDenominator (d p : ℝ) : ℝ :=
  (5/6-d)*(3-p-4*p/countLambda)+d*(1-p)*(2-4*p/countLambda)
def countNumerator (d p : ℝ) : ℝ :=
  (1-d)*countDenominator d p+(5/6-d)*d*(1-p)*(1-2*p*countB/countLambda)
def criticalRow (theta height d p : ℝ) : ℝ :=
  (1+d)/2+(11/3-4*theta)*(1/2+d*p)-5/12*height-
    d*p*((physicalB*height-4*(11/3-4*theta))/physicalLambda)/2+
    3/4*height*(countNumerator d p/countDenominator d p)
def halfRowNumerator (v d : ℝ) : ℝ :=
  ((1+d)/2+(11/3-4*criticalTheta v)*(1/2+d/2)-5/12*criticalHeight v-
    d*((physicalB*criticalHeight v-4*(11/3-4*criticalTheta v))/physicalLambda)/4)*
      halfDenominator d+3/4*criticalHeight v*halfNumerator d

theorem half_denominator_eq (d : ℝ) :
    countDenominator d (1/2) = halfDenominator d := by
  unfold countDenominator countLambda halfDenominator
  ring

theorem half_numerator_eq (d : ℝ) :
    countNumerator d (1/2) = halfNumerator d := by
  unfold countNumerator countDenominator countLambda countB halfNumerator
  ring

theorem half_row_eq (v d : ℝ) (hd : halfDenominator d ≠ 0) :
    criticalRow (criticalTheta v) (criticalHeight v) d (1/2) =
      halfRowNumerator v d/halfDenominator d := by
  unfold criticalRow halfRowNumerator
  rw [half_denominator_eq, half_numerator_eq]
  field_simp
  <;> ring

theorem critical_half_factorization (v d : ℝ)
    (hroot : parameterPolynomial v = 0) :
    criticalTheta v*halfDenominator d-halfRowNumerator v d =
      squareCoefficient v*(d-v)^2 := by
  dsimp only [criticalTheta, halfDenominator, halfRowNumerator, criticalHeight,
    squareCoefficient, physicalB, physicalLambda, halfNumerator]
  unfold parameterPolynomial at hroot
  linear_combination (((582909361/92730625658866578757130737493667968961302089513457859883731841112295435026952508715700:ℝ) * (-647647773920692213208414358559023658975235954831132175 + (-193117560865854433271506040398124131023525521751262462 * v) + (386235121731708866543012080796248262047051043502524924 * d)))) * hroot

theorem critical_parameter_guards {v : ℝ}
    (hv : (4636766567303565669606137753427/10000000000000000000000000000000:ℝ) ≤ v ∧
      v ≤ 4636766567303565669606137753428/10000000000000000000000000000000) :
    87482852/100000000 < criticalTheta v ∧ criticalTheta v < 87482853/100000000 ∧
    7970705/10000000 < criticalHeight v ∧ criticalHeight v < 7970707/10000000 ∧
    0 < squareCoefficient v := by
  rcases hv with ⟨hlo,hhi⟩
  norm_num [criticalTheta,criticalHeight,squareCoefficient]
  constructor
  · linarith only [hlo,hhi]
  constructor
  · linarith only [hlo,hhi]
  constructor
  · linarith only [hlo,hhi]
  constructor <;> linarith only [hlo,hhi]

theorem half_denominator_pos {d : ℝ} (hd : d ≤ 1/2) :
    0 < halfDenominator d := by
  norm_num [halfDenominator]
  linarith only [hd]

/-- The touching critical row has a positive quadratic-square deficit.
    Every denominator and parameter sign used here is explicit. -/
theorem critical_half_bound {v d : ℝ}
    (hv : (4636766567303565669606137753427/10000000000000000000000000000000:ℝ) ≤ v ∧
      v ≤ 4636766567303565669606137753428/10000000000000000000000000000000)
    (hroot : parameterPolynomial v = 0) (hd : d ≤ 1/2) :
    criticalRow (criticalTheta v) (criticalHeight v) d (1/2) ≤ criticalTheta v := by
  have hj := half_denominator_pos hd
  rw [half_row_eq v d hj.ne']
  apply (div_le_iff₀ hj).mpr
  have hfactor := critical_half_factorization v d hroot
  have hpos := mul_nonneg (critical_parameter_guards hv).2.2.2.2.le (sq_nonneg (d-v))
  linarith only [hfactor,hpos]

end
end Sil.Uneven.Critical
end

/- Original module: Candidate.Uneven.CriticalParameter. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Sil.Uneven.Critical
noncomputable section

def parameterA : ℝ := 91804891419376373332989
def parameterB : ℝ := 191011230531473313491625
def parameterC : ℝ := 68829760479687653132500
def parameterDiscriminant : ℝ := parameterB^2-4*parameterA*parameterC
def criticalParameter : ℝ := (parameterB-Real.sqrt parameterDiscriminant)/(2*parameterA)
def parameterLower : ℝ := 4636766567303565669606137753427/10000000000000000000000000000000
def parameterUpper : ℝ := 4636766567303565669606137753428/10000000000000000000000000000000

theorem parameter_a_pos : 0 < parameterA := by norm_num [parameterA]
theorem parameter_discriminant_pos : 0 < parameterDiscriminant := by
  norm_num [parameterDiscriminant,parameterA,parameterB,parameterC]

theorem critical_parameter_polynomial : parameterPolynomial criticalParameter = 0 := by
  have hs := Real.sq_sqrt parameter_discriminant_pos.le
  have ha : parameterA ≠ 0 := parameter_a_pos.ne'
  have hmain : parameterA*criticalParameter^2-parameterB*criticalParameter+parameterC=0 := by
    dsimp only [criticalParameter]
    field_simp
    change Real.sqrt parameterDiscriminant^2=parameterB^2-4*parameterA*parameterC at hs
    nlinarith only [hs]
  simpa only [parameterPolynomial,parameterA,parameterB,parameterC,sub_eq_add_neg,
    neg_mul,add_assoc,add_comm,add_left_comm] using hmain

theorem critical_parameter_isolation : parameterLower < criticalParameter ∧
    criticalParameter < parameterUpper := by
  have hs := Real.sq_sqrt parameter_discriminant_pos.le
  have hn := Real.sqrt_nonneg parameterDiscriminant
  have hlo0 : 0 < parameterB-2*parameterA*parameterLower := by
    norm_num [parameterA,parameterB,parameterLower]
  have hhi0 : 0 < parameterB-2*parameterA*parameterUpper := by
    norm_num [parameterA,parameterB,parameterUpper]
  have hlo : parameterDiscriminant < (parameterB-2*parameterA*parameterLower)^2 := by
    norm_num [parameterDiscriminant,parameterA,parameterB,parameterC,parameterLower]
  have hhi : (parameterB-2*parameterA*parameterUpper)^2 < parameterDiscriminant := by
    norm_num [parameterDiscriminant,parameterA,parameterB,parameterC,parameterUpper]
  have hslo : Real.sqrt parameterDiscriminant < parameterB-2*parameterA*parameterLower := by
    nlinarith only [hs,hn,hlo0,hlo]
  have hshi : parameterB-2*parameterA*parameterUpper < Real.sqrt parameterDiscriminant := by
    nlinarith only [hs,hn,hhi0,hhi]
  constructor
  · unfold criticalParameter
    rw [lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) parameter_a_pos)]
    linarith only [hslo]
  · unfold criticalParameter
    rw [div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) parameter_a_pos)]
    linarith only [hshi]

theorem theta_endpoint_polynomial {v : ℝ} (hroot : parameterPolynomial v = 0) :
    quadA*(criticalTheta v)^2-quadB*criticalTheta v+quadC=0 := by
  unfold quadA quadB quadC criticalTheta
  unfold parameterPolynomial at hroot
  linear_combination (31193771087113702371801295290000808181469/75222846364626430310413988706191:ℝ)*hroot

theorem critical_theta_eq_endpoint : criticalTheta criticalParameter = endpoint := by
  have hguard := critical_parameter_guards
    ⟨critical_parameter_isolation.1.le,critical_parameter_isolation.2.le⟩
  have ht : criticalTheta criticalParameter < (9/10:ℝ) :=
    hguard.2.1.trans (by norm_num)
  have he : endpoint < (9/10:ℝ) := endpoint_isolation.2.trans (by norm_num [upper])
  have hp := theta_endpoint_polynomial critical_parameter_polynomial
  have hfactor : (criticalTheta criticalParameter-endpoint)*
      (quadA*(criticalTheta criticalParameter+endpoint)-quadB)=0 := by
    nlinarith only [hp,endpoint_polynomial]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hsum : criticalTheta criticalParameter+endpoint < (9/5:ℝ) := by linarith
    have hlt := mul_lt_mul_of_pos_left hsum quadA_pos
    have hconst : quadA*(9/5:ℝ) < quadB := by norm_num [quadA,quadB]
    linarith only [hlt,hconst,h]

/-- An unconditional algebraic inequality for the critical half-amplitude row.
    The analytic source hypotheses and complementary parameter cover are separate. -/
theorem endpoint_critical_half_bound {d : ℝ} (hd : d ≤ 1/2) :
    criticalRow endpoint (criticalHeight criticalParameter) d (1/2) ≤ endpoint := by
  have h := critical_half_bound
    ⟨critical_parameter_isolation.1.le,critical_parameter_isolation.2.le⟩
    critical_parameter_polynomial hd
  simpa only [critical_theta_eq_endpoint] using h

end
end Sil.Uneven.Critical
end

/- Original module: Candidate.Uneven.CriticalAmplitude. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Sil.Uneven.Critical
noncomputable section

def amplitudeDifference (t h d p : ℝ) : ℝ := ((1/2344740912781485349088718983624400:ℝ) * d * (53699821264136213558751925034493750 + (-61914399156305436207151156038633000 * d) + (-58581623197239505700456645492175000 * t) + (-37191024589446474260542308344831250 * p) + (-3334796598336340696452165084438375 * h) + (16173788260260380313460154409934200 * (d ^ 2)) + (-17644132647556778523774713901746400 * t * (d ^ 2)) + (-17430779281954524256188000000000000 * (d ^ 2) * (p ^ 2)) + (-3407381508434069884525337347190154 * h * (d ^ 2)) + (2123419153681256764678451370794750 * h * p) + (6470922761255361326874677762376735 * d * h) + (6523877779524601717872691994481000 * d * p) + (16173788260260380313460154409934200 * p * (d ^ 2)) + (23149301001681283689150000000000000 * d * (p ^ 2)) + (40572026824850699193318881830725000 * p * t) + (67542980897787748589619442951236000 * d * t) + (-25253782910925036751800000000000000 * d * t * (p ^ 2)) + (-17644132647556778523774713901746400 * p * t * (d ^ 2)) + (-7116957577663201874042936721252000 * d * p * t) + (-3198716943027188367062349644573145 * d * h * p) + (-535668686821317097281750000000000 * d * h * (p ^ 2)) + (403343610572028310042860000000000 * h * (d ^ 2) * (p ^ 2)) + (1464576860477135401199931353472666 * h * p * (d ^ 2)) + (19015395580314026461296000000000000 * t * (d ^ 2) * (p ^ 2))))

theorem amplitude_corner_00 {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 ≤ amplitudeDifference (21870713/25000000:ℝ) (1594141/2000000:ℝ) d p := by
  let x : ℝ := (d-117/256)/(9/256)
  let y : ℝ := (p-63/128)/(1/128)
  have hx : 0 ≤ x := by dsimp [x]; linarith [hd.1]
  have hx' : 0 ≤ 1-x := by dsimp [x]; linarith [hd.2]
  have hy : 0 ≤ y := by dsimp [y]; linarith [hp.1]
  have hy' : 0 ≤ 1-y := by dsimp [y]; linarith [hp.2]
  have hid : amplitudeDifference (21870713/25000000:ℝ) (1594141/2000000:ℝ) d p =
    (431800107289284452356091501628322800844031207/12432821651839096257579248687902663639040000000:ℝ)*x^0*(1-x)^3*y^0*(1-y)^2 +
    (7695673932171208273195049473086191893779992711/111895394866551866318213238191123972751360000000:ℝ)*x^0*(1-x)^3*y^1*(1-y)^1 +
    (59526940598227122067502575683391996740907607/1748365544789872911222081846736312074240000000:ℝ)*x^0*(1-x)^3*y^2*(1-y)^0 +
    (677967375767008495411243803842524671220007359/6216410825919548128789624343951331819520000000:ℝ)*x^1*(1-x)^2*y^0*(1-y)^2 +
    (12084420721214748456983928793345997840418647647/55947697433275933159106619095561986375680000000:ℝ)*x^1*(1-x)^2*y^1*(1-y)^1 +
    (93486022537349253250233798039519120766374319/874182772394936455611040923368156037120000000:ℝ)*x^1*(1-x)^2*y^2*(1-y)^0 +
    (353778042666980642529904489044774132911032861/3108205412959774064394812171975665909760000000:ℝ)*x^2*(1-x)^1*y^0*(1-y)^2 +
    (6306597984073048600488567582963987503581797373/27973848716637966579553309547780993187840000000:ℝ)*x^2*(1-x)^1*y^1*(1-y)^1 +
    (48793722828172242570945614590723205682978541/437091386197468227805520461684078018560000000:ℝ)*x^2*(1-x)^1*y^2*(1-y)^0 +
    (61338936236539943420142964292578199524856573/1554102706479887032197406085987832954880000000:ℝ)*x^3*(1-x)^0*y^0*(1-y)^2 +
    (1093557384833566756934508319778589172488450269/13986924358318983289776654773890496593920000000:ℝ)*x^3*(1-x)^0*y^1*(1-y)^1 +
    (8461592341660533231762911319551810321763533/218545693098734113902760230842039009280000000:ℝ)*x^3*(1-x)^0*y^2*(1-y)^0 := by
    dsimp [amplitudeDifference,x,y]
    ring
  rw [hid]
  positivity

theorem amplitude_corner_01 {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 ≤ amplitudeDifference (21870713/25000000:ℝ) (7970707/10000000:ℝ) d p := by
  let x : ℝ := (d-117/256)/(9/256)
  let y : ℝ := (p-63/128)/(1/128)
  have hx : 0 ≤ x := by dsimp [x]; linarith [hd.1]
  have hx' : 0 ≤ 1-x := by dsimp [x]; linarith [hd.2]
  have hy : 0 ≤ y := by dsimp [y]; linarith [hp.1]
  have hy' : 0 ≤ 1-y := by dsimp [y]; linarith [hp.2]
  have hid : amplitudeDifference (21870713/25000000:ℝ) (7970707/10000000:ℝ) d p =
    (10794994783818895748878795536272337091529836813/310820541295977406439481217197566590976000000000:ℝ)*x^0*(1-x)^3*y^0*(1-y)^2 +
    (192391706822394360401776499478144012441669221101/2797384871663796657955330954778099318784000000000:ℝ)*x^0*(1-x)^3*y^1*(1-y)^1 +
    (1488172414998871077890826804723435467390293981/43709138619746822780552046168407801856000000000:ℝ)*x^0*(1-x)^3*y^2*(1-y)^0 +
    (16949172754044959155884103883222630137196813141/155410270647988703219740608598783295488000000000:ℝ)*x^1*(1-x)^2*y^0*(1-y)^2 +
    (302110309538556315028829909947921393742372358197/1398692435831898328977665477389049659392000000000:ℝ)*x^1*(1-x)^2*y^1*(1-y)^1 +
    (2337148942616483360258193923067341524543815077/21854569309873411390276023084203900928000000000:ℝ)*x^1*(1-x)^2*y^2*(1-y)^0 +
    (8844445360326022434601222450871382714106469279/77705135323994351609870304299391647744000000000:ℝ)*x^2*(1-x)^1*y^0*(1-y)^2 +
    (157664847400245494080982076586812941450706429503/699346217915949164488832738694524829696000000000:ℝ)*x^2*(1-x)^1*y^1*(1-y)^1 +
    (1219842276246393594816352931901088161810274703/10927284654936705695138011542101950464000000000:ℝ)*x^2*(1-x)^1*y^2*(1-y)^0 +
    (1533472475097372234729403211064834763672424767/38852567661997175804935152149695823872000000000:ℝ)*x^3*(1-x)^0*y^0*(1-y)^2 +
    (27338917951074789459374821705224022844691423199/349673108957974582244416369347262414848000000000:ℝ)*x^3*(1-x)^0*y^1*(1-y)^1 +
    (211539678970139509285311599210391037597640239/5463642327468352847569005771050975232000000000:ℝ)*x^3*(1-x)^0*y^2*(1-y)^0 := by
    dsimp [amplitudeDifference,x,y]
    ring
  rw [hid]
  positivity

theorem amplitude_corner_10 {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 ≤ amplitudeDifference (87482853/100000000:ℝ) (1594141/2000000:ℝ) d p := by
  let x : ℝ := (d-117/256)/(9/256)
  let y : ℝ := (p-63/128)/(1/128)
  have hx : 0 ≤ x := by dsimp [x]; linarith [hd.1]
  have hx' : 0 ≤ 1-x := by dsimp [x]; linarith [hd.2]
  have hy : 0 ≤ y := by dsimp [y]; linarith [hp.1]
  have hy' : 0 ≤ 1-y := by dsimp [y]; linarith [hp.2]
  have hid : amplitudeDifference (87482853/100000000:ℝ) (1594141/2000000:ℝ) d p =
    (2158998515660756314629364797809854565468667163/62164108259195481287896243439513318195200000000:ℝ)*x^0*(1-x)^3*y^0*(1-y)^2 +
    (38478333509778805931213309773096866373591303291/559476974332759331591066190955619863756800000000:ℝ)*x^0*(1-x)^3*y^1*(1-y)^1 +
    (297634422295665406874884308037377795223362091/8741827723949364556110409233681560371200000000:ℝ)*x^0*(1-x)^3*y^2*(1-y)^0 +
    (3389833851014183018560953086288875541511254291/31082054129597740643948121719756659097600000000:ℝ)*x^1*(1-x)^2*y^0*(1-y)^2 +
    (60422049443833104767407986448021408719099834227/279738487166379665795533095477809931878400000000:ℝ)*x^1*(1-x)^2*y^1*(1-y)^1 +
    (467429692176788941274054933483673471363990947/4370913861974682278055204616840780185600000000:ℝ)*x^1*(1-x)^2*y^2*(1-y)^0 +
    (1768888703408493073927187818815730028089419929/15541027064798870321974060859878329548800000000:ℝ)*x^2*(1-x)^1*y^0*(1-y)^2 +
    (31532962912750429984531755725948827100288210873/139869243583189832897766547738904965939200000000:ℝ)*x^2*(1-x)^1*y^1*(1-y)^1 +
    (243968404473930540531822195951635375474594633/2185456930987341139027602308420390092800000000:ℝ)*x^2*(1-x)^1*y^2*(1-y)^0 +
    (306694430545221729426676467611185716542042617/7770513532399435160987030429939164774400000000:ℝ)*x^3*(1-x)^0*y^0*(1-y)^2 +
    (5467782441473009271401158356203937310749283609/69934621791594916448883273869452482969600000000:ℝ)*x^3*(1-x)^0*y^1*(1-y)^1 +
    (42307926910996134918369587090808025347836329/1092728465493670569513801154210195046400000000:ℝ)*x^3*(1-x)^0*y^2*(1-y)^0 := by
    dsimp [amplitudeDifference,x,y]
    ring
  rw [hid]
  positivity

theorem amplitude_corner_11 {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 ≤ amplitudeDifference (87482853/100000000:ℝ) (7970707/10000000:ℝ) d p := by
  let x : ℝ := (d-117/256)/(9/256)
  let y : ℝ := (p-63/128)/(1/128)
  have hx : 0 ≤ x := by dsimp [x]; linarith [hd.1]
  have hx' : 0 ≤ 1-x := by dsimp [x]; linarith [hd.2]
  have hy : 0 ≤ y := by dsimp [y]; linarith [hp.1]
  have hy' : 0 ≤ 1-y := by dsimp [y]; linarith [hp.2]
  have hid : amplitudeDifference (87482853/100000000:ℝ) (7970707/10000000:ℝ) d p =
    (10794984679890566013123331984613539897772392453/310820541295977406439481217197566590976000000000:ℝ)*x^0*(1-x)^3*y^0*(1-y)^2 +
    (192391526067008183227966811516473546965125919781/2797384871663796657955330954778099318784000000000:ℝ)*x^0*(1-x)^3*y^1*(1-y)^1 +
    (1488171011521520060577683952825524524984414261/43709138619746822780552046168407801856000000000:ℝ)*x^0*(1-x)^3*y^2*(1-y)^0 +
    (16949157614940661863407774218603891064252900621/155410270647988703219740608598783295488000000000:ℝ)*x^1*(1-x)^2*y^0*(1-y)^2 +
    (302110038727353127441271622354378491327405338157/1398692435831898328977665477389049659392000000000:ℝ)*x^1*(1-x)^2*y^1*(1-y)^1 +
    (2337146840066696735372623639497730862204411837/21854569309873411390276023084203900928000000000:ℝ)*x^1*(1-x)^2*y^2*(1-y)^0 +
    (8844437810693971740989549318830679531777747399/77705135323994351609870304299391647744000000000:ℝ)*x^2*(1-x)^1*y^0*(1-y)^2 +
    (157664712362171428991426665642457389362602549543/699346217915949164488832738694524829696000000000:ℝ)*x^2*(1-x)^1*y^1*(1-y)^1 +
    (1219841227911740233201823546891184897108784343/10927284654936705695138011542101950464000000000:ℝ)*x^2*(1-x)^1*y^2*(1-y)^0 +
    (1533471221909982296359211441806308358261223527/38852567661997175804935152149695823872000000000:ℝ)*x^3*(1-x)^0*y^0*(1-y)^2 +
    (27338895537600666893017905491778980086226584519/349673108957974582244416369347262414848000000000:ℝ)*x^3*(1-x)^0*y^1*(1-y)^1 +
    (211539504983606853083086751675635906292733559/5463642327468352847569005771050975232000000000:ℝ)*x^3*(1-x)^0*y^2*(1-y)^0 := by
    dsimp [amplitudeDifference,x,y]
    ring
  rw [hid]
  positivity

private theorem affine_box_nonneg (c x y t h : ℝ)
    (ht : (87482852/100000000:ℝ) ≤ t ∧ t ≤ 87482853/100000000)
    (hh : (7970705/10000000:ℝ) ≤ h ∧ h ≤ 7970707/10000000)
    (h00 : 0 ≤ c+x*(87482852/100000000)+y*(7970705/10000000))
    (h01 : 0 ≤ c+x*(87482852/100000000)+y*(7970707/10000000))
    (h10 : 0 ≤ c+x*(87482853/100000000)+y*(7970705/10000000))
    (h11 : 0 ≤ c+x*(87482853/100000000)+y*(7970707/10000000)) :
    0 ≤ c+x*t+y*h := by
  let a : ℝ := (t-87482852/100000000)/(1/100000000)
  let b : ℝ := (h-7970705/10000000)/(2/10000000)
  have ha : 0 ≤ a := by dsimp [a]; linarith only [ht.1]
  have ha' : 0 ≤ 1-a := by dsimp [a]; linarith only [ht.2]
  have hb : 0 ≤ b := by dsimp [b]; linarith only [hh.1]
  have hb' : 0 ≤ 1-b := by dsimp [b]; linarith only [hh.2]
  have hid : c+x*t+y*h =
      (1-a)*(1-b)*(c+x*(87482852/100000000)+y*(7970705/10000000))+
      (1-a)*b*(c+x*(87482852/100000000)+y*(7970707/10000000))+
      a*(1-b)*(c+x*(87482853/100000000)+y*(7970705/10000000))+
      a*b*(c+x*(87482853/100000000)+y*(7970707/10000000)) := by
    dsimp [a,b]
    ring
  rw [hid]
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg ha' hb') h00)
    (mul_nonneg (mul_nonneg ha' hb) h01))
    (mul_nonneg (mul_nonneg ha hb') h10))
    (mul_nonneg (mul_nonneg ha hb) h11)

theorem amplitude_difference_affine (t h d p : ℝ) :
    amplitudeDifference t h d p = amplitudeDifference 0 0 d p+
      (amplitudeDifference 1 0 d p-amplitudeDifference 0 0 d p)*t+
      (amplitudeDifference 0 1 d p-amplitudeDifference 0 0 d p)*h := by
  dsimp [amplitudeDifference]
  ring

attribute [local irreducible] amplitudeDifference

theorem amplitude_difference_nonneg {t h d p : ℝ}
    (ht : (87482852/100000000:ℝ) ≤ t ∧ t ≤ 87482853/100000000)
    (hh : (7970705/10000000:ℝ) ≤ h ∧ h ≤ 7970707/10000000)
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 ≤ amplitudeDifference t h d p := by
  rw [amplitude_difference_affine]
  have h00 := amplitude_corner_00 hd hp
  have h01 := amplitude_corner_01 hd hp
  have h10 := amplitude_corner_10 hd hp
  have h11 := amplitude_corner_11 hd hp
  rw [amplitude_difference_affine] at h00 h01 h10 h11
  apply affine_box_nonneg _ _ _ t h ht hh
  · norm_num at h00 ⊢
    exact h00
  · norm_num at h01 ⊢
    exact h01
  · norm_num at h10 ⊢
    exact h10
  · norm_num at h11 ⊢
    exact h11

theorem count_denominator_pos {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 < countDenominator d p := by
  have hd0 : 0 < d := by linarith [hd.1]
  have hd1 : 0 < 5/6-d := by linarith [hd.2]
  have hp1 : 0 < 1-p := by linarith [hp.2]
  have hD : 0 < 3-p-4*p/countLambda := by norm_num [countLambda]; linarith [hp.2]
  have hA : 0 < 2-4*p/countLambda := by norm_num [countLambda]; linarith [hp.2]
  exact add_pos (mul_pos hd1 hD) (mul_pos (mul_pos hd0 hp1) hA)

theorem amplitude_difference_identity (t h d p : ℝ)
    (hj : countDenominator d p ≠ 0) (hk : countDenominator d (1/2) ≠ 0) :
    (criticalRow t h d (1/2)-criticalRow t h d p)*
      countDenominator d p*countDenominator d (1/2) =
      (1/2-p)*amplitudeDifference t h d p := by
  unfold criticalRow amplitudeDifference
  field_simp
  <;> dsimp [countDenominator,countNumerator,physicalB,physicalLambda,countB,countLambda,amplitudeDifference]
  <;> ring

theorem critical_row_le_half {t h d p : ℝ}
    (ht : (87482852/100000000:ℝ) ≤ t ∧ t ≤ 87482853/100000000)
    (hh : (7970705/10000000:ℝ) ≤ h ∧ h ≤ 7970707/10000000)
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    criticalRow t h d p ≤ criticalRow t h d (1/2) := by
  have hj := count_denominator_pos hd hp
  have hk := count_denominator_pos hd ⟨by norm_num,le_refl _⟩
  have hid := amplitude_difference_identity t h d p hj.ne' hk.ne'
  have hnonneg := mul_nonneg (sub_nonneg.mpr hp.2) (amplitude_difference_nonneg ht hh hd hp)
  have hmul : 0 ≤ (criticalRow t h d (1/2)-criticalRow t h d p)*
      (countDenominator d p*countDenominator d (1/2)) := by nlinarith only [hid,hnonneg]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (mul_pos hj hk)).mp hmul)

/-- The entire critical rectangle, including its touching point. -/
theorem endpoint_critical_rectangle {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    criticalRow endpoint (criticalHeight criticalParameter) d p ≤ endpoint := by
  have hg := critical_parameter_guards
    ⟨critical_parameter_isolation.1.le,critical_parameter_isolation.2.le⟩
  rw [critical_theta_eq_endpoint] at hg
  exact (critical_row_le_half ⟨hg.1.le,hg.2.1.le⟩
    ⟨hg.2.2.1.le,hg.2.2.2.1.le⟩ hd hp).trans
      (endpoint_critical_half_bound (hd.2.trans (by norm_num)))

end
end Sil.Uneven.Critical
end
