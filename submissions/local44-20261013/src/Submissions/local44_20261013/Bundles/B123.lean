/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B029
import Submissions.local44_20261013.Bundles.B033
import Submissions.local44_20261013.Bundles.B038
import Submissions.local44_20261013.Bundles.B045
import Submissions.local44_20261013.Bundles.B047
import Submissions.local44_20261013.Bundles.B072
import Submissions.local44_20261013.Bundles.B074
import Submissions.local44_20261013.Bundles.B076
import Submissions.local44_20261013.Bundles.B077
import Submissions.local44_20261013.Bundles.B079
import Submissions.local44_20261013.Bundles.B122

/- BEGIN ORIGINAL MODULE Global.Detector.Mesh ; sha256 c2dae43a911f9f118e7536cb1912d27b88db9b3734ee9d55bd3796fd2e933679 -/
section



/-! A common source mesh for the unchanged detector moments and the new
physical numerator. It is chosen before the finite slot family. -/
noncomputable section
namespace Submission20261012.Global

def sourceMesh (t : ℝ) : ℝ :=
  min (Cycle25.sourceMesh t) (OAI.SevenEighths.Local44.Physical.transportMomentMesh t)

theorem sourceMesh_pos {t : ℝ} (ht : 0 < t) : 0 < sourceMesh t :=
  lt_min (Cycle25.sourceMesh_pos ht)
    (OAI.SevenEighths.Local44.Physical.transportMomentMesh_pos t ht)

theorem sourceMesh_le_old (t : ℝ) : sourceMesh t ≤ Cycle25.sourceMesh t :=
  min_le_left _ _

theorem sourceMesh_le_transport (t : ℝ) :
    sourceMesh t ≤ OAI.SevenEighths.Local44.Physical.transportMomentMesh t :=
  min_le_right _ _

end Submission20261012.Global

#print axioms Submission20261012.Global.sourceMesh_pos
end
/- END ORIGINAL MODULE Global.Detector.Mesh -/

/- BEGIN ORIGINAL MODULE Global.Numerator.LocalSelection ; sha256 249c7b7b1078c5457a6ba81512396977f364849dd1853e1538d17d990e7783d3 -/
section





/-! Whole-slot selection for the local physical transport capacity, on literal
full amplitude classes. Error slots keep their lengths in the weighted mean. -/
noncomputable section
open scoped Classical BigOperators
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator OAI.SevenEighths
open HeckeDetectorSlotSelection HeckeDetectorPhysicalSelection
open _root_.Local44.Physical
open OAI.SevenEighths.Local44.Physical

theorem local_source_bare_window (d : ℝ)
    (hdlo : Endpoint.junction ≤ d) (hdhi : d ≤ h+rowExtension) :
    BareWindow (1-ly/d) := by
  have hd : 0 < d := by
    norm_num [Endpoint.junction, Endpoint.h] at hdlo
    linarith
  constructor
  · have hb : ly/d ≤ 581/1000 := by
      apply (div_le_iff₀ hd).mpr
      norm_num [ly,Endpoint.y,Endpoint.h,Endpoint.ell,Endpoint.junction] at *
      linarith
    linarith
  · have hb : (578:ℝ)/1000 ≤ ly/d := by
      apply (le_div_iff₀ hd).mpr
      norm_num [ly,h,rowExtension,Endpoint.y,Endpoint.h,Endpoint.ell,Endpoint.zeta] at *
      linarith
    linarith

theorem local_baseCapacity_le_supply (d : ℝ) (hd : (1/2:ℝ) ≤ d) :
    _root_.Local44.Physical.baseCapacity (1-ly/d) ≤ ell/d := by
  have hdp : 0 < d := by linarith
  have hh : (2*ly-d)/(22/5:ℝ) ≤ ell := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<22/5)).mpr
    norm_num [ly,ell,Endpoint.y,Endpoint.h,Endpoint.ell]
    linarith
  have hh' := div_le_div_of_nonneg_right hh hdp.le
  convert hh' using 1
  unfold _root_.Local44.Physical.baseCapacity
  field_simp
  <;> ring

theorem highData_transport_selection {Δ : ℝ} (D : HighParameters.HighData Δ)
    (hfine : ∀j,D.ell j ≤ transportMomentMesh D.t/200)
    (d v δ : ℝ) (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (hbare : BareWindow (1-ly/d))
    (main : Finset (Fin D.N)) (g : Fin D.N→ℝ)
    (hg : ∀j,0 ≤ g j ∧ g j ≤ δ/2) (herror : ∀j,j∉main → g j=0) :
    let widths := fun j=> D.ell j/d
    let q := weightedMean Finset.univ widths g
    let mesh := transportMomentMesh D.t
    q = (∑j,widths j*g j)/(ell/d) ∧ 0 ≤ q ∧ q ≤ δ/2 ∧
    ∃selected : Finset (Fin D.N),selected⊆main ∧ (∀j∈selected,0 < g j) ∧
      (∑j∈selected,widths j) ≤ transportCapacity (1-ly/d) v ∧
      q*transportCapacity (1-ly/d) v-(δ/2)*mesh ≤ ∑j∈selected,widths j*g j ∧
      ∀U : ℝ,1 ≤ U → ∀Q : Fin D.N→ℂ,
        (∀j,0 < g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) →
        U^(2*q*transportCapacity (1-ly/d) v-δ*mesh) ≤ ‖∏j∈selected,Q j‖^2 := by
  have hd0 : 0 < d := by linarith
  let widths := fun j=> D.ell j/d
  have hsum : (∑j,widths j)=ell/d := by
    dsimp [widths]
    rw [←Finset.sum_div,D.slots_sum]
  have hL : 0 < ∑j,widths j := by rw [hsum];exact div_pos ell_pos hd0
  have hw (j : Fin D.N) : 0 ≤ widths j := (div_pos (D.slots_bounds j).1 hd0).le
  have hmesh := transportMomentMesh_pos D.t D.t_pos
  have hwm (j : Fin D.N) : widths j ≤ transportMomentMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have hj := hfine j
    nlinarith only [hj,hd,hmesh]
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds Finset.univ widths g δ
    (fun j _=> hw j) hL (fun j _=> hg j)
  obtain ⟨T,_,hT,hTpos,hTz,hgain,hspike⟩ := transport_whole_slots Finset.univ main widths g
    (1-ly/d) v δ (transportMomentMesh D.t) hbare hv hδ hmesh.le
    (fun j _=> hw j) (fun j _=> hwm j)
    (by rw [hsum];exact local_baseCapacity_le_supply d hd)
    (fun j _=> hg j) (fun j _=> herror j)
  refine ⟨?_,hq,hqδ,T,hT,hTpos,hTz,hgain,?_⟩
  · unfold weightedMean
    rw [hsum]
  · intro U hU Q hQ
    exact hspike U hU Q (fun j _=> hQ j)

end Submission20261012.Global.Numerator
end
/- END ORIGINAL MODULE Global.Numerator.LocalSelection -/

/- BEGIN ORIGINAL MODULE Global.Numerator.Scalar.SourceLoss ; sha256 b9d4ec28489b59b9feb52a1f5ce3c19f297ff6b5832093623c9ebd21749166b4 -/
section



noncomputable section
namespace Submission20261012.Global.Numerator.Scalar
open Cycle25
open OAI.SevenEighths.Local44.Physical
open Cycle25.Numerator.Scalar (sourceMesh_le)
/-- Annular padding uses the actual moment parameter. The common mesh cost
remains explicit until the loss budget is applied. -/
def weightedSourceLoss (kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus : ℝ) : ℝ :=
  3*t+(17/25)*t+
    d*(2*eps+massEps+(3*(159*epsilon+9*t)+momentEps)/4+
      delta*mesh/4+delta*boxWidth/4+q*annulus/(6*kap))+t*ell

theorem weightedSourceLoss_le
    (kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus : ℝ)
    (hk : 7/10 ≤ kap) (_hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 3/4)
    (hq : 0 ≤ q) (hq1 : q ≤ delta/2)
    (hepsilon : 0 ≤ epsilon) (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (hmesh : 0 ≤ mesh) (hmesh1 : mesh ≤ t)
    (hmass : 0 ≤ massEps) (hmass1 : massEps ≤ t)
    (hmoment : 0 ≤ momentEps) (hmoment1 : momentEps ≤ 2*t)
    (hbox : 0 ≤ boxWidth) (hbox1 : boxWidth ≤ t)
    (hannulus : 0 ≤ annulus) (hannulus1 : annulus ≤ t) :
    weightedSourceLoss kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus ≤
      120*epsilon+2*eps+13*t := by
  have hk0 : 0 < 6*kap := by linarith
  have hdm : delta*mesh ≤ (3/4)*t :=
    (mul_le_mul_of_nonneg_left hmesh1 hdelta).trans
      (mul_le_mul_of_nonneg_right hdelta1 ht)
  have hdb : delta*boxWidth ≤ (3/4)*t :=
    (mul_le_mul_of_nonneg_left hbox1 hdelta).trans
      (mul_le_mul_of_nonneg_right hdelta1 ht)
  have hqt : q*annulus ≤ (3/8)*t :=
    (mul_le_mul_of_nonneg_left hannulus1 hq).trans
      (mul_le_mul_of_nonneg_right (by linarith : q ≤ 3/8) ht)
  have hann : q*annulus/(6*kap) ≤ t/10 := by
    apply (div_le_iff₀ hk0).2
    have hm := mul_le_mul_of_nonneg_right hk ht
    nlinarith
  have hinner : 0 ≤ 2*eps+massEps+(3*(159*epsilon+9*t)+momentEps)/4+
      delta*mesh/4+delta*boxWidth/4+q*annulus/(6*kap) := by positivity
  have hdinner := mul_le_mul_of_nonneg_right hd1 hinner
  have hell : t*ell ≤ t/5 := by
    have hm := mul_le_mul_of_nonneg_left ell_lt_one_fifth.le ht
    linarith
  unfold weightedSourceLoss
  nlinarith only [hdinner,hdm,hdb,hann,hmass1,hmoment1,hepsilon,ht,hell]

theorem weighted_source_packet_exponent
    (kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus : ℝ)
    (hk : kap ≠ 0) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    -ly/2-(4/25)*ell+(3+17/25)*t+t*ell+
      d*(2*eps+massEps+q*(ell/d)-
        q*((2*(ly/d)-1)/(6*kap)-annulus/(3*kap))/2+
        (3*(OAI.SevenEighths.Cycle25DetectorRowCount.rowCount delta (q/delta) kap+
          159*epsilon+9*t)+1+momentEps)/4+
        delta*mesh/4+delta*boxWidth/4-17/50) =
      numeratorExponent kap d delta (q/delta)+
        weightedSourceLoss kap d delta q epsilon eps t mesh massEps momentEps boxWidth annulus := by
  unfold numeratorExponent weightedSourceLoss
  have hq : delta*(q/delta)=q := by field_simp
  rw [hq]
  field_simp
  ring

theorem weighted_source_uniform_packet_budget {beta : ℝ}
    (D : HighParameters.HighData (beta-theta)) :
    16*D.e+(120*D.ε+2*D.eps+15*D.t)+D.t ≤ (beta-theta)/50 := by
  have hn : 0 ≤ D.eps*(D.N:ℝ) := mul_nonneg D.eps_pos.le (Nat.cast_nonneg _)
  have htell : 0 ≤ D.t*ell := mul_nonneg D.t_pos.le ell_pos.le
  have hb := D.central_budget
  nlinarith only [hb,hn,htell,D.e_pos,D.epsilon_pos,D.eps_pos,D.t_pos]

theorem weighted_source_packet_fixed_budget {beta : ℝ}
    (D : HighParameters.HighData (beta-theta)) (d delta q : ℝ)
    (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 3/4)
    (hq : 0 ≤ q) (hq1 : q ≤ delta/2) :
    16*D.e+weightedSourceLoss D.momentKappa d delta q D.ε D.eps D.t
      (_root_.Cycle25.sourceMesh D.t) D.t (2*D.t) D.t D.t+D.t ≤ (beta-theta)/50 := by
  have hl := weightedSourceLoss_le D.momentKappa d delta q D.ε D.eps D.t
    (_root_.Cycle25.sourceMesh D.t) D.t (2*D.t) D.t D.t D.momentKappa_lo hd hd1 hdelta hdelta1 hq hq1
    D.epsilon_pos.le D.eps_pos.le D.t_pos.le (_root_.Cycle25.sourceMesh_pos D.t_pos).le
    (sourceMesh_le D.t_pos) D.t_pos.le le_rfl (mul_nonneg (by norm_num) D.t_pos.le) le_rfl
    D.t_pos.le le_rfl D.t_pos.le le_rfl
  linarith [weighted_source_uniform_packet_budget D, D.t_pos]


def localSourceLoss (d delta epsilon eps t mesh : ℝ) : ℝ :=
  3*t+(17/25)*t+
    d*(2*eps+t+(3*(159*epsilon+9*t)+2*t)/4+delta*mesh/4+delta*t)+t*ell

theorem localSourceLoss_le (d delta epsilon eps t mesh : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 3/4)
    (hepsilon : 0 ≤ epsilon) (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (hmesh : 0 ≤ mesh) (hmesh1 : mesh ≤ t) :
    localSourceLoss d delta epsilon eps t mesh ≤ 120*epsilon+2*eps+15*t := by
  have hdm : delta*mesh ≤ (3/4)*t :=
    (mul_le_mul_of_nonneg_left hmesh1 hdelta).trans
      (mul_le_mul_of_nonneg_right hdelta1 ht)
  have hdt : delta*t ≤ (3/4)*t := mul_le_mul_of_nonneg_right hdelta1 ht
  have hi : 0 ≤ 2*eps+t+(3*(159*epsilon+9*t)+2*t)/4+delta*mesh/4+delta*t := by positivity
  have hdinner := mul_le_mul_of_nonneg_right hd1 hi
  have hell : t*ell ≤ t/5 := by
    have hh := mul_le_mul_of_nonneg_left ell_lt_one_fifth.le ht
    linarith
  unfold localSourceLoss
  nlinarith only [hdinner,hdm,hdt,hell,hepsilon,ht]

theorem local_source_packet_fixed_budget {beta : ℝ}
    (D : HighParameters.HighData (beta-theta)) (d delta : ℝ)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 3/4) :
    16*D.e+localSourceLoss d delta D.ε D.eps D.t (transportMomentMesh D.t)+D.t ≤
      (beta-theta)/50 := by
  have hm : transportMomentMesh D.t ≤ D.t :=
    (transportMomentMesh_le_old D.t).trans (sourceMesh_le D.t_pos)
  have hh := localSourceLoss_le d delta D.ε D.eps D.t (transportMomentMesh D.t)
    hd hd1 hdelta hdelta1 D.epsilon_pos.le D.eps_pos.le D.t_pos.le
    (transportMomentMesh_pos D.t D.t_pos).le hm
  linarith [weighted_source_uniform_packet_budget D, D.t_pos]

def piecewiseSourceLoss (kap d delta q epsilon eps t : ℝ) : ℝ :=
  if Endpoint.junction ≤ d then localSourceLoss d delta epsilon eps t (transportMomentMesh t)
    else weightedSourceLoss kap d delta q epsilon eps t (_root_.Cycle25.sourceMesh t) t (2*t) t t

/-- The actual local/old packet ledger spends only gap-dependent losses, while
retaining the strict scalar reserve. -/
theorem source_packet_certificate
    (D : HighParameters.HighData (OAI.SevenEighths.HeckeZeroSupremum.beta-theta))
    (hbeta : theta < OAI.SevenEighths.HeckeZeroSupremum.beta)
    (d a q : ℝ) (hd : 1/2 ≤ d) (hdtop : d ≤ h+3*D.t)
    (ha : 1/3 ≤ 2*a-1) (ha1 : a ≤ 7/8)
    (hq : 0 ≤ q) (hq1 : q ≤ (2*a-1)/2) :
    piecewiseNumeratorExponent D.momentKappa d (2*a-1) (q/(2*a-1))+
      piecewiseSourceLoss D.momentKappa d (2*a-1) q D.ε D.eps D.t ≤
      signal OAI.SevenEighths.HeckeZeroSupremum.beta-
        (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2-
        weightedSourceSZExponent a D.e-D.t := by
  have hdelta : 0 < 2*a-1 := by linarith
  have hdelta1 : 2*a-1 ≤ 3/4 := by linarith
  have hd1 : d ≤ 1 := by linarith [h_interval.2,D.t_small]
  have hp : 0 ≤ q/(2*a-1) ∧ q/(2*a-1) ≤ 1/2 :=
    ⟨div_nonneg hq hdelta.le,(div_le_iff₀ hdelta).2 (by linarith)⟩
  have hwide : d ≤ h+rowExtension := by linarith [D.weighted_top]
  have hb := source_numerator_feedback hbeta hd hwide ⟨hdelta.le,hdelta1⟩ hp
  rw [←D.momentKappa_exact] at hb
  have hbudget : 16*D.e+piecewiseSourceLoss D.momentKappa d (2*a-1) q D.ε D.eps D.t+D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/50 := by
    unfold piecewiseSourceLoss
    split_ifs
    · exact local_source_packet_fixed_budget D d (2*a-1) (by linarith) hd1 hdelta.le hdelta1
    · exact weighted_source_packet_fixed_budget D d (2*a-1) q (by linarith) hd1 hdelta.le hdelta1 hq hq1
  have heq : (1+(2*a-1))/2=a := by ring
  rw [heq] at hb
  have hsz : weightedSourceSZExponent a D.e=weightedSourceSZExponent a 0+16*D.e := by
    unfold weightedSourceSZExponent
    ring
  rw [hsz]
  linarith

end Submission20261012.Global.Numerator.Scalar
#print axioms Submission20261012.Global.Numerator.Scalar.source_packet_certificate
end
/- END ORIGINAL MODULE Global.Numerator.Scalar.SourceLoss -/

/- BEGIN ORIGINAL MODULE Global.Weighted.Input ; sha256 05211ec088e8c9500a5135eb2fe03d83f706cab86c82a66e94abb71e4191bc44 -/
section




/-! Final quantifier-preserving assembly of the actual integrated weighted
source estimate.  The analytic input below is explicit and is not asserted
by this module.  The transformation adds only the two external integrals
and the actual source normalizer. -/
namespace Submission20261012.Global
open OAI OAI.SevenEighths
noncomputable section
open scoped Classical BigOperators
open Filter
namespace ProbeAssembly
open HeckeFamily Cycle25ProbeFinalAssembly
open Cycle25ProbeHighRowFamily

def FullWAnalyticInput : Prop :=
  ∀_hβ : Submission20261012.Global.theta < HeckeZeroSupremum.beta,
  ∀D : Submission20261012.Global.HighParameters.HighData (HeckeZeroSupremum.beta-Submission20261012.Global.theta),
  (∀j,D.ell j ≤ OAI.SevenEighths.Local44.Physical.transportMomentMesh D.t/200) →
  ∀F : WeightedSourceData D.toMomentData,
  ∀counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t,
  ∃Jw : ℝ,0 ≤ Jw ∧
  ∀τ : ℝ,0 < τ → τ < (1/200:ℝ)/2 → 4*τ < (1/200)*D.cost →
    τ < D.t → 2*τ ≤ D.t → τ*(2+4*D.eps) < D.t → 2*τ*(1+Jw) ≤ D.t →
  ∀n : ℕ,∀η : Character,∃Cw : ℝ,0 ≤ Cw ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1 ≤ C0 →
    weighted_SourceMomentBound F D.momentKappa counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
    FullWCellsAt D F η Z τ n Cw C0

/-- The literal integrated source target, with its height degree chosen
before the contour height parameter and its constant independent of C0. -/
def IntegratedFullWAnalyticInput : Prop :=
  ∀_hβ : Submission20261012.Global.theta < HeckeZeroSupremum.beta,
  ∀D : Submission20261012.Global.HighParameters.HighData (HeckeZeroSupremum.beta-Submission20261012.Global.theta),
  (∀j,D.ell j ≤ OAI.SevenEighths.Local44.Physical.transportMomentMesh D.t/200) →
  ∀F : WeightedSourceData D.toMomentData,
  ∀counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t,
  ∃Jw : ℝ,0 ≤ Jw ∧
  ∀τ : ℝ,0 < τ → τ < (1/200:ℝ)/2 → 4*τ < (1/200)*D.cost →
    τ < D.t → 2*τ ≤ D.t → τ*(2+4*D.eps) < D.t → 2*τ*(1+Jw) ≤ D.t →
  ∀n : ℕ,∀η : Character,∃Cw : ℝ,0 ≤ Cw ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1 ≤ C0 →
    weighted_SourceMomentBound F D.momentKappa counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
    IntegratedWeightedCellsAt D F η Z τ n Cw C0

/-- Integrating and normalizing preserves every required uniformity,
including a fixed degree chosen before tau and linear dependence on C0. -/
theorem fullW_input_of_integrated_input (hinput : IntegratedFullWAnalyticInput) :
    FullWAnalyticInput := by
  intro hβ D hfine F counts
  obtain ⟨Jw,hJw,hinput⟩ := hinput hβ D hfine F counts
  obtain ⟨C,hC,hfinish⟩ := fullWCellsAt_of_integrated D F
  refine ⟨Jw,hJw,?_⟩
  intro τ hτ hτsmall hτcost hτt hτ2 hτeps hτJ n η
  obtain ⟨Cw,hCw,hinput⟩ := hinput τ hτ hτsmall hτcost hτt hτ2 hτeps hτJ n η
  refine ⟨C*Cw,mul_nonneg hC.le hCw,?_⟩
  filter_upwards [hinput,hfinish τ hτ n] with Z hi hf
  intro C0 hC0 hmom
  exact hf η Cw C0 hCw (zero_le_one.trans hC0) (hi C0 hC0 hmom)

end ProbeAssembly
end
end Submission20261012.Global

#print axioms Submission20261012.Global.ProbeAssembly.fullW_input_of_integrated_input
end
/- END ORIGINAL MODULE Global.Weighted.Input -/

/- BEGIN ORIGINAL MODULE Physical.LocalRetained ; sha256 59336d47ff688dcacc9651e8962ed02dcb2a01bfd4585c536e756c496becf08a -/
section



/-! Actual rowwise primitive restoration using the local/old/empty Fourier
dispatch. This retains the full natural coefficient packet and its conductor. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Local44.Physical
open Cycle25WeightedNumeratorReflection Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyReferenceLowWindow CenteredMomentNaturalPrimitive
local notation "O" => HeckeFamily.O

theorem certified_transport_actual_retained_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (epsilon Cscale xi : ℝ) (hepsilon : 0 < epsilon) (hCscale : 0 < Cscale) (hxi : 0 < xi) :
    ∃ degree : ℕ, ∃ H : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ (τ ψ : rows → Character) (G : rows → 𝓢(ℝ,ℂ)) (X : rows → ℝ) (m n B Rcap : ℝ),
      (∀ i, ∀ k : O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) k = elementCoeff (τ i) k) →
      (∀ i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 →
      _root_.Local44.Physical.BareWindow n → n ≤ m+xi → 0 < B →
      (∀ i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ B) →
      1 ≤ Rcap → (∀ i, (Ideal.absNorm (∏ P ∈ sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Rcap) →
      (∀ i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏ P ∈ sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀ T : Finset (Fin D.N), ∀ width : T → ℝ, ∀ z : T → ℂ, ∀ height : ℝ,
      (∀ i, 0 < width i) → (∀ i, width i ≤ transportMomentMesh D.t) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      (∑ i, width i) ≤ _root_.Local44.Physical.transportCapacity n (m+xi-n) →
      (∑ i : rows, ‖retainedSchwartz (τ i) (ψ i) (G i) (X i) (U^(xi/4))‖^4 *
        ‖∏ s, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤
      C*Rcap^epsilon*B^4*(1+2*((m+xi)*Real.log U))^2*(1+height)^degree*U^(1+D.t) := by
  obtain ⟨degree,J,Cp,hCp,hpositive⟩ := certified_transport_reflected_fourier_moment F hbeta hbetaTop
  obtain ⟨H,Cr,hCr,hretained⟩ := actual_retained_uniform_fourth epsilon hepsilon 2 J (by norm_num)
  refine ⟨degree,H,Cr*Cp,by positivity,?_⟩
  filter_upwards [hpositive,eventually_retained_log_interval Cscale xi hCscale hxi]
    with U hp hg
  have hU := hp.1
  have hUpos := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ G X m n B Rcap he hX hm hmmax hn hnm hB hG hRcap hR
    hcombined T width z height hw hwmax hreal hheight hzim hcapacity
  let nupper := m+xi
  have hnupper : 0 ≤ nupper := by dsimp [nupper]; linarith
  let P (i : rows) := ∏ s, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let E := Cp*(1+height)^degree*U^(1+D.t)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hinterval : 0 ≤ nupper*Real.log U := mul_nonneg hnupper (Real.log_pos hU).le
  have hgeom (i : rows) (a : CenteredMomentReflectionWeightedEnergy.Index (sourcePrimes (τ i) (ψ i)))
      (hY : 0 < dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
      (ha : a.2 ∈ CenteredMomentReflectedTruncation.retainedAnnuli (U^(xi/4))
        (dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2) hY) :
      Real.log (dyadicScale a.2*dualScale (τ i) (ψ i) (X i) a.1.1 a.1.2)
        ∈ Set.Icc 0 (nupper*Real.log U) :=
    hg.2 (τ i) (ψ i) (X i) m (hX i) (hcombined i) a hY ha
  have hpoly (i : rows) (W : ℝ → ℂ) (x freq : ℝ) :
      polynomial (τ i).inverse false W x 0 freq =
      polynomial (rowCharacter F.S F.exclusions.prime i.val).inverse false W x 0 freq :=
    (Cycle25.Weighted.RowConductor.polynomial_eq_of_elementCoeff_eq _ _
      (Cycle25.Weighted.RowConductor.inverse_elementCoeff_eq _ _ (he i)) false W x 0 freq).symm
  have hmoment (v w : ℝ) (j k : Fin 2) (x : ℝ) (hx : x ∈ Set.Icc 0 (nupper*Real.log U))
      (y : ℝ) (hy : y ∈ Set.Icc 0 (nupper*Real.log U)) :
      (∑ i : rows, ‖polynomial (τ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
        (Real.exp x) 0 (2*Real.pi*v) *
        polynomial (τ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) k)
        (Real.exp y) 0 (2*Real.pi*w) * P i‖^2) ≤
      E*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
    have hxlen := reflection_window_length U nupper x hU hnupper hx
    have hylen := reflection_window_length U nupper y hU hnupper hy
    have hxge : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx.1
    have hyge : 1 ≤ Real.exp y := Real.one_le_exp_iff.mpr hy.1
    have hxcap : Real.logb U (Real.exp x) ≤ n+(m+xi-n) := by
      have hn' : n+(m+xi-n) = nupper := by dsimp [nupper]; ring
      rw [hn']
      simpa only [length,max_eq_right hxge] using hxlen.1
    have hycap : Real.logb U (Real.exp y) ≤ n+(m+xi-n) := by
      have hn' : n+(m+xi-n) = nupper := by dsimp [nupper]; ring
      rw [hn']
      simpa only [length,max_eq_right hyge] using hylen.1
    simp_rw [hpoly]
    have hb := hp.2 rows hrows n (m+xi-n) hn (by linarith) (by linarith)
      T width z height hw hwmax hreal hheight hzim hcapacity
      (Real.exp x) (Real.exp y) hxge hyge hxcap hycap j k v w
    rw [←Finset.sum_coe_sort rows] at hb
    exact hb
  have hresult := hretained G τ ψ P X (fun _ => U^(xi/4)) 0 (nupper*Real.log U) B E Rcap
    hX hinterval hgeom hB hE hG hRcap hR hmoment
  convert hresult using 1 <;> dsimp [E,nupper] <;> ring

end SevenEighths.Local44.Physical
end
end OAI

#print axioms OAI.SevenEighths.Local44.Physical.certified_transport_actual_retained_fourth
end
/- END ORIGINAL MODULE Physical.LocalRetained -/

/- BEGIN ORIGINAL MODULE Global.Final.Data ; sha256 9d770e1056b9eadaea87543cc56a3dd085b6446c2fddee6547469ec33dd89287 -/
section




/-! Actual fixed source data and both certified count families are chosen
before the contour height.  Apache-2.0 attribution: weighted upstream
HighRows/ConditionalFinal, revision 2fd60c0926b66ea18d7436f5ed55250fd006ab5d. -/
namespace Submission20261012.Global.FinalAssembly
noncomputable section
open scoped Classical
open Filter OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.Cycle25ProbeFinalAssembly

structure ChosenData where
  D : HighParameters.HighData (HeckeZeroSupremum.beta-theta)
  fine : ∀j,D.ell j ≤ sourceMesh D.t/200
  fine_old : ∀j,D.ell j ≤ Cycle25.sourceMesh D.t/200
  fine_transport : ∀j,D.ell j ≤ OAI.SevenEighths.Local44.Physical.transportMomentMesh D.t/200
  F : WeightedSourceData D.toMomentData
  counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t
  oldcounts : ProbeFinalAssembly.CountParameters F.modulus ⊤ D.t
  J : ℝ
  Jo : ℝ
  J_nonneg : 0 ≤ J
  Jo_nonneg : 0 ≤ Jo
  moments : ∀η : Character,∃C : ℝ,0 < C ∧
    ∀τ : ℝ,0 < τ → τ ≤ 1 → ∀ᶠZ : ℝ in atTop,
      weighted_SourceMomentBound F D.momentKappa counts η Z τ
        (C*(1+Z^(2*τ))^J) (Z^(2*τ))
  old_moments : ∀η : Character,∃C : ℝ,0 < C ∧
    ∀τ : ℝ,0 < τ → τ ≤ 1 → ∀ᶠZ : ℝ in atTop,
      old_sourceMomentBound F oldcounts η Z τ
        (C*(1+Z^(2*τ))^Jo) (Z^(2*τ))

theorem exists_chosen_data (hβ : theta < HeckeZeroSupremum.beta) :
    Nonempty ChosenData := by
  obtain ⟨hk,hk1,hbeta51⟩ := moment_parameter_gates hβ
  obtain ⟨D,hfine⟩ := HighParameters.exists_high_data_fine
    (HeckeZeroSupremum.beta-theta) (sub_pos.mpr hβ)
    (2*HeckeZeroSupremum.beta-1) hk hk1 le_rfl rfl sourceMesh
    (fun _ ht=> sourceMesh_pos ht)
  have hfine_old : ∀j,D.ell j ≤ Cycle25.sourceMesh D.t/200 :=
    fun j => (hfine j).trans (div_le_div_of_nonneg_right (sourceMesh_le_old D.t) (by norm_num))
  have hfine_transport : ∀j,D.ell j ≤ OAI.SevenEighths.Local44.Physical.transportMomentMesh D.t/200 :=
    fun j => (hfine j).trans (div_le_div_of_nonneg_right (sourceMesh_le_transport D.t) (by norm_num))
  obtain ⟨F⟩ := weighted_exists_source_data D.toMomentData
  obtain ⟨counts⟩ := weighted_fresh_count_parameters F
  obtain ⟨oldcounts⟩ := weighted_source_count_parameters F
  obtain ⟨J,hJ,hmom⟩ := weighted_actual_source_moments F D.momentKappa
    D.momentKappa_lo D.momentKappa_hi hbeta51 D.momentKappa_beta counts hfine_old
  obtain ⟨Jo,hJo,hmomOld⟩ := weighted_actual_old_source_moments F D.momentKappa
    D.momentKappa_lo D.momentKappa_hi hbeta51 D.momentKappa_beta oldcounts hfine_old
  exact ⟨⟨D,hfine,hfine_old,hfine_transport,F,counts,oldcounts,J,Jo,hJ,hJo,hmom,hmomOld⟩⟩
end
end Submission20261012.Global.FinalAssembly

#print axioms Submission20261012.Global.FinalAssembly.exists_chosen_data
end
/- END ORIGINAL MODULE Global.Final.Data -/
