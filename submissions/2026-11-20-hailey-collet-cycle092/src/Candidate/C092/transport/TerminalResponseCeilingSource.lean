/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine prime upper bound compares measured response with the actual
zero band, uniformly through an early finite bank. -/
import Candidate.C092.transport.TerminalResponseCeilingBank

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalResponseCeiling
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.Cycle61Moment.LowBranch
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot]
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_TerminalResponseCeilingSource_fd334dedd6ae4827_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- No comparison estimate is assumed. The actual source is called at every
member of a finite early bank. One common C precedes every live state,
zero band, prime-slot array, pitch and row. The payment is unchanged. -/
theorem actual_zero_band_ceiling
    (price : ℝ) (hprice : 0 < price)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character, ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ Cslot : ℝ, C ≤ Cslot →
      ∀ s : NaturalState U Bmask bΦ, s.width ≤ Mcap →
      ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
        (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 7/8 →
      ∀ (θ : Slot→RayQuotient.Characters M H) (w σ v : Slot→ℝ) (t : ℝ),
        (∀ j, 0 ≤ w j) → (∀ j, w j/d ≤ Rwidth) →
        (∀ j, σmin ≤ σ j) → (∀ j, σ j ≤ σmax) →
        (∀ j, |t+v j|+U^τ/2 ≤ (3*i+2 : ℕ)*U^τ) →
        (3+(3*i+2 : ℕ)*U^τ)^2 ≤ (U^d)^η →
      ∀ z : O, s.radial.keep z → ActualLow M H hH s η₀ hQM hQη a e
        (3*(i+1 : ℕ)*U^τ) z →
      originalResponse s.character s.mask 1 t U (Cslot*U^(2*ε*d)) w
        (originalPools M H B U w) (originalCoefficients M H hH η₀ θ W U w σ v)
        (fun j=>U^(w j)) z ≤ (2*a-1)+price := by
  obtain ⟨J,q,hq,hcover⟩ := finite_upper_bank hprice
  have hsrc (j : Fin J) := actual_low_response (Slot:=Slot) M H hH (q j) (hq j).1 (hq j).2
    W A B hA hWs hW Rwidth dmax τ ε e κ η σmin σmax bΦ Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  choose C hC hsource using hsrc
  let Cmax := 1+∑ j,C j
  have hCsum : 0 ≤ ∑ j,C j := Finset.sum_nonneg (fun j _ => (hC j).le)
  have hCmax : 0 < Cmax := by dsimp [Cmax]; linarith
  have hCj (j : Fin J) : C j ≤ Cmax := by
    have hj := Finset.single_le_sum (f:=C) (fun k _ => (hC k).le) (Finset.mem_univ j)
    dsimp [Cmax]
    linarith
  refine ⟨Cmax,hCmax,?_⟩
  intro η₀
  have hall := Filter.eventually_all.mpr (fun j : Fin J => hsource j η₀)
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with U hall hU
  refine ⟨hU,?_⟩
  intro Cslot hCslot s hs hQM hQη a i ha ha' θ w σ v t hw hwr hσlo hσhi hfreq hheight z hz hlow
  have hν : 0 ≤ 2*a-1 := by linarith only [ha]
  have hνhi : 2*a-1 ≤ 3/4 := by linarith only [ha']
  obtain ⟨j,hνq,hqν⟩ := hcover (2*a-1) hν hνhi
  have haq : a ≤ (1+q j)/2 := by linarith only [hνq]
  have hslots := ((hall j).2 s hs hQM hQη a i ha haq θ w σ v t hw hwr hσlo hσhi
    hfreq hheight z hz hlow).1
  have hp : 0 < Cslot*U^(2*ε*d) :=
    mul_pos (hCmax.trans_le hCslot) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
  have htop : 0 ≤ (2*a-1)+price := by positivity
  apply (originalResponse_bounded s.character s.mask 1 t U (Cslot*U^(2*ε*d))
    ((2*a-1)+price) w (originalPools M H B U w)
    (originalCoefficients M H hH η₀ θ W U w σ v) (fun j=>U^(w j)) z hU hp hw htop ?_).2
  intro k
  have hb := hslots k (Finset.mem_univ _)
  have hCjk : C j ≤ Cslot := (hCj j).trans hCslot
  have heq : q j*w k ≤ ((2*a-1)+price)*w k := mul_le_mul_of_nonneg_right hqν (hw k)
  have hup := Real.rpow_le_rpow_of_exponent_le hU.le heq
  have hUpay : 0 ≤ U^(2*ε*d) := Real.rpow_nonneg (zero_lt_one.trans hU).le _
  have hUq : 0 ≤ U^(q j*w k) := Real.rpow_nonneg (zero_lt_one.trans hU).le _
  exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_right hCjk hUpay) hup hUq hp.le)

#print axioms actual_zero_band_ceiling
end
end QRH.Cycle092.TerminalResponseCeiling
