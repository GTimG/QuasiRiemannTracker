import Candidate.Target836.Detector836.Schedule
import Candidate.Affine.Masked
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Detector836
noncomputable section
open Cycle63.Arithmetic.Bernstein
def acceptedComparePower (δ p : ℝ) : ℝ := (1509473/72420000)*δ^1*p^4 +
  (-4964370336071/18105000000000)*δ^1*p^3 +
  (138754949/301750000)*δ^1*p^2 +
  (-1246098284643/6035000000000)*δ^1*p^1 +
  (197701564937/1278000000000)*δ^0*p^3 +
  (-1562628556429/5431500000000)*δ^0*p^2 +
  (963195873929/7242000000000)*δ^0*p^1
def acceptedCompareMinimum : ℝ := 1880719925709689/434520000000000000
theorem acceptedCompareMinimum_pos : 0 < acceptedCompareMinimum := by norm_num [acceptedCompareMinimum]
def acceptedCompareCoefficients0 : Fin 3 → Fin 5 → ℝ := ![
  ![(259998139419014518261/57936000000000000000000 : ℝ), (12457827759638907278057/2780928000000000000000000 : ℝ), (93267640259504360429/20856960000000000000000 : ℝ), (310337101812030343/69523200000000000000 : ℝ), (387225763430371/86904000000000000 : ℝ)],
  ![(1281395214195344671877/289680000000000000000000 : ℝ), (15349515142744766667031/3476160000000000000000000 : ℝ), (6759800416294642571/1533600000000000000000 : ℝ), (382371016444690169/86904000000000000000 : ℝ), (477106092857693/108630000000000000 : ℝ)],
  ![(1262799731295616752449/289680000000000000000000 : ℝ), (60506982343763596945963/13904640000000000000000000 : ℝ), (452994655318549587511/104284800000000000000000 : ℝ), (88663683676315861/20448000000000000000 : ℝ), (1880719925709689/434520000000000000 : ℝ)]]
theorem acceptedCompareCoefficients0_lower (i : Fin 3) (j : Fin 5) :
    acceptedCompareMinimum ≤ acceptedCompareCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [acceptedCompareMinimum,acceptedCompareCoefficients0]
theorem acceptedCompareIdentity0 (δ p : ℝ) :
    acceptedComparePower δ p = tensor24 acceptedCompareCoefficients0
      ((δ-89/200)/(451/1000-89/200)) ((p-199/400)/(1/2-199/400)) := by
  norm_num [acceptedComparePower,tensor24,basis2,basis4,acceptedCompareCoefficients0,Fin.sum_univ_succ]
  ring
theorem acceptedCompareBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (89/200) (451/1000)) (hp : p ∈ Set.Icc (199/400) (1/2)) :
    0 < acceptedComparePower δ p := by
  rw [acceptedCompareIdentity0]
  exact tensor24_pos acceptedCompareMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    acceptedCompareCoefficients0_lower
theorem acceptedCompare_binding (δ p : ℝ) : acceptedComparePower δ p =
    oldNum p*DetectorAffine.JN δ p-2*(1-p)*DetectorAffine.cN p*
      ((5/6-δ)*oldDen p+δ*oldNum p) := by
  unfold acceptedComparePower oldNum oldDen kStar DetectorAffine.JN DetectorAffine.DN
    DetectorAffine.aN DetectorAffine.cN DetectorAffine.lam DetectorAffine.Bc
  ring
theorem accepted_compare {δ p : ℝ} (h : InAcceptedRegion δ p) : DetectorAffine.RNew δ p ≤ ROld δ p := by
  have hJ := DetectorAffine.region_JN_pos (accepted_region_subset h)
  have hR := DetectorAffine.region_RNew_mul (accepted_region_subset h)
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hc := acceptedCompareBox0_pos ⟨h1, h2⟩ ⟨h3, h4⟩
  rw [acceptedCompare_binding] at hc
  have hD := oldDen_pos (p:=p) (by linarith) h4
  have hN := oldNum_nonneg (p:=p) (by linarith) h4
  have hcN := DetectorAffine.cN_pos (p:=p) (by linarith) h4
  set c := oldNum p/oldDen p with hcdef
  have hc0 : 0 ≤ c := div_nonneg hN hD.le
  have hcD : c*oldDen p = oldNum p := div_mul_cancel₀ _ hD.ne'
  have hV : 0 < 5/6-δ := by linarith
  have hS : 0 < (5/6-δ)+δ*c := by nlinarith
  -- DetectorAffine.RNew - (1-δ) = Vδ(1-p)DetectorAffine.cN/DetectorAffine.JN ≤ δ c V/(2 S)
  have hlhs : DetectorAffine.RNew δ p-(1-δ) = (5/6-δ)*δ*(1-p)*DetectorAffine.cN p/DetectorAffine.JN δ p := by unfold DetectorAffine.RNew; ring
  have hrhs : ROld δ p-(1-δ) = δ*c*(5/6-δ)/(2*((5/6-δ)+δ*c)) := by unfold ROld; ring
  have key : (5/6-δ)*δ*(1-p)*DetectorAffine.cN p/DetectorAffine.JN δ p ≤ δ*c*(5/6-δ)/(2*((5/6-δ)+δ*c)) := by
    rw [div_le_div_iff₀ hJ (by positivity)]
    -- cross-multiplied: Vδ(1-p)DetectorAffine.cN * 2S ≤ δ c V DetectorAffine.JN; divide by Vδ ≥ 0 and use certificate
    have hcert : 2*(1-p)*DetectorAffine.cN p*((5/6-δ)+δ*c) ≤ c*DetectorAffine.JN δ p := by
      have e1 : (c*DetectorAffine.JN δ p-2*(1-p)*DetectorAffine.cN p*((5/6-δ)+δ*c))*oldDen p =
          oldNum p*DetectorAffine.JN δ p-2*(1-p)*DetectorAffine.cN p*((5/6-δ)*oldDen p+δ*oldNum p) := by
        linear_combination (DetectorAffine.JN δ p-2*(1-p)*DetectorAffine.cN p*δ)*hcD
      have := (mul_pos_iff_of_pos_right hD).mp (e1 ▸ hc)
      linarith
    have hVδ : 0 ≤ (5/6-δ)*δ := mul_nonneg hV.le (by linarith)
    have := mul_le_mul_of_nonneg_left hcert hVδ
    nlinarith
  linarith

theorem ROld_eq_target (δ p : ℝ) : ROld δ p = countingR0 kStar δ p := by
  unfold ROld countingR0 rowDen countingCoefficient countingDen oldNum oldDen kStar
  ring_nf
theorem RNew_antitone {δ p p' : ℝ} (h : Detector836.InRegion δ p)
    (h' : Detector836.InRegion δ p') (hpp : p ≤ p') :
    Detector836.RNew δ p' ≤ Detector836.RNew δ p := by
  have hJ := Detector836.region_JN_pos h
  have hJ' := Detector836.region_JN_pos h'
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨_, _, h3', h4'⟩ := h'
  -- (1-p)cN(p) JN(p') - (1-p')cN(p') JN(p) = (p'-p) Q, Q multilinear and positive on the box
  set Q : ℝ := (-39790318729/39176284900)*δ^1*p^1*p'^1 +
    (2987047/1979300)*δ^1*p^1*p'^0 +
    (2987047/1979300)*δ^1*p^0*p'^1 +
    (-4945647/1979300)*δ^1*p^0*p'^0 +
    (39277561271/47011541880)*δ^0*p^1*p'^1 +
    (-987047/791720)*δ^0*p^1*p'^0 +
    (-987047/791720)*δ^0*p^0*p'^1 +
    (4919741/2375160)*δ^0*p^0*p'^0 with hQ
  have hid : (1-p)*Detector836.cN p*Detector836.JN δ p'-
      (1-p')*Detector836.cN p'*Detector836.JN δ p = (p'-p)*Q := by
    rw [hQ]
    unfold Detector836.cN Detector836.JN Detector836.DN Detector836.aN
      Detector836.lam Detector836.Bc
    ring
  have hQpos : 0 ≤ Q := by
    let u : ℝ := (δ-451/1000)/(39/1000)
    let v : ℝ := (p-49/100)/(1/100)
    let w : ℝ := (p'-49/100)/(1/100)
    have hu : 0 ≤ u ∧ u ≤ 1 := by dsimp [u]; constructor <;> linarith
    have hv : 0 ≤ v ∧ v ≤ 1 := by dsimp [v]; constructor <;> linarith
    have hw : 0 ≤ w ∧ w ≤ 1 := by dsimp [w]; constructor <;> linarith
    have hu0 : 0 ≤ u := hu.1
    have hv0 : 0 ≤ v := hv.1
    have hw0 : 0 ≤ w := hw.1
    have hu1 : 0 ≤ 1-u := by linarith [hu.2]
    have hv1 : 0 ≤ 1-v := by linarith [hv.2]
    have hw1 : 0 ≤ 1-w := by linarith [hw.2]
    have hidentity : Q = (188153836149231921/391762849000000000)*(1-u)*(1-v)*(1-w) +
      (11199637112946661/23505770940000000)*(1-u)*(1-v)*w +
      (11199637112946661/23505770940000000)*(1-u)*v*(1-w) +
      (74072874726521/156705139600000)*(1-u)*v*w +
      (16884779182585329/39176284900000000)*u*(1-v)*(1-w) +
      (1005054678897589/2350577094000000)*u*(1-v)*w +
      (1005054678897589/2350577094000000)*u*v*(1-w) +
      (6647346740729/15670513960000)*u*v*w := by
      rw [hQ]
      dsimp [u,v,w]
      ring
    rw [hidentity]
    positivity
  have hcross : (1-p')*Detector836.cN p'*Detector836.JN δ p ≤
      (1-p)*Detector836.cN p*Detector836.JN δ p' := by
    have := mul_nonneg (sub_nonneg.mpr hpp) hQpos
    linarith
  have hfrac : (1-p')*Detector836.cN p'/Detector836.JN δ p' ≤
      (1-p)*Detector836.cN p/Detector836.JN δ p := by
    rw [div_le_div_iff₀ hJ' hJ]; linarith
  have hV : 0 ≤ (5/6-δ)*δ := mul_nonneg (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left hfrac hV
  unfold Detector836.RNew
  have e1 : (5/6-δ)*δ*(1-p')*Detector836.cN p'/Detector836.JN δ p' =
      (5/6-δ)*δ*((1-p')*Detector836.cN p'/Detector836.JN δ p') := by ring
  have e2 : (5/6-δ)*δ*(1-p)*Detector836.cN p/Detector836.JN δ p =
      (5/6-δ)*δ*((1-p)*Detector836.cN p/Detector836.JN δ p) := by ring
  rw [e1, e2]; linarith



end
end Detector836
#print axioms Detector836.accepted_compare
#print axioms Detector836.RNew_antitone
