import WeightedQRH.HighRows.WeightedSourceFinish
import WeightedQRH.HighRows.WeightedSourceSelection

/-! Explicit loss accounting for the actual weighted source.  This module
checks the proposed analytic ledger; it does not assume that a row bound
with this ledger has already been obtained. -/
noncomputable section
namespace WeightedQRH
open OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands
open OAI.SevenEighths.CenteredMomentEnergyWidthRanges
open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

theorem weighted_detectorMesh_le {t : ℝ} (ht : 0 < t) :
    weighted_detectorMesh t ≤ t := by
  obtain ⟨_,_,ha,_,_,hm,_,hr,_,_⟩ := bounds 2
    (finalSourceCap 2 0 1 (t/4)) (3/4) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by norm_num) (by positivity)
  change mesh 2 (finalSourceCap 2 0 1 (t/4)) (3/4) (t/4) ≤ t
  linarith

/-- Count prefactor, physical frequency, scalar, coefficient mass, Holder,
selection, dilation, annular padding, and full-amplitude upper slack. -/
def weightedSourceLoss (d δ q ε eps t mesh massEps momentEps boxWidth annulus : ℝ) : ℝ :=
  3*t+(17/25)*t+
    d*(2*eps+massEps+(3*(159*ε+9*t)+momentEps)/4+
      δ*mesh/4+δ*boxWidth/4+2*q*annulus/9)+t*ell

/-- The ledger is uniform across all retained dyads and all masked bins.
The annular capacity padding is included explicitly. -/
theorem weightedSourceLoss_le (d δ q ε eps t mesh massEps momentEps boxWidth annulus : ℝ)
    (hd : 0 ≤ d) (hd' : d ≤ 1) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4)
    (hq : 0 ≤ q) (hq' : q ≤ δ/2)
    (hε : 0 ≤ ε) (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (hmesh : 0 ≤ mesh) (hmesh' : mesh ≤ t)
    (hmass : 0 ≤ massEps) (hmass' : massEps ≤ t)
    (hmoment : 0 ≤ momentEps) (hmoment' : momentEps ≤ 2*t)
    (hbox : 0 ≤ boxWidth) (hbox' : boxWidth ≤ t)
    (hannulus : 0 ≤ annulus) (hannulus' : annulus ≤ t) :
    weightedSourceLoss d δ q ε eps t mesh massEps momentEps boxWidth annulus ≤
      120*ε+2*eps+13*t := by
  have hdm : δ*mesh ≤ (3/4)*t :=
    (mul_le_mul_of_nonneg_left hmesh' hδ).trans
      (mul_le_mul_of_nonneg_right hδ' ht)
  have hdb : δ*boxWidth ≤ (3/4)*t :=
    (mul_le_mul_of_nonneg_left hbox' hδ).trans
      (mul_le_mul_of_nonneg_right hδ' ht)
  have hqt : q*annulus ≤ (3/8)*t :=
    (mul_le_mul_of_nonneg_left hannulus' hq).trans
      (mul_le_mul_of_nonneg_right (by linarith : q ≤ 3/8) ht)
  have hinner : 0 ≤ 2*eps+massEps+(3*(159*ε+9*t)+momentEps)/4+
      δ*mesh/4+δ*boxWidth/4+2*q*annulus/9 := by positivity
  have hdinner := mul_le_mul_of_nonneg_right hd' hinner
  unfold weightedSourceLoss ell
  nlinarith only [hdinner,hdm,hdb,hqt,hmass',hmoment',hε,ht]

/-- The concrete choices used in the numerator packet fit the existing
parameter budget, with the fixed height cost still reserved separately. -/
theorem weighted_source_packet_fixed_budget {Δ : ℝ} (D : HighParameters.HighData Δ)
    (d δ q : ℝ) (hd : 0 ≤ d) (hd' : d ≤ 1)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4) (hq : 0 ≤ q) (hq' : q ≤ δ/2) :
    16*D.e+
      weightedSourceLoss d δ q D.ε D.eps D.t (weighted_detectorMesh D.t)
        D.t (2*D.t) D.t D.t+D.t ≤ 1/40000 := by
  apply OAI.SevenEighths.WeightedHighFinalAssembly.weighted_source_fixed_budget
  have hl := weightedSourceLoss_le d δ q D.ε D.eps D.t (weighted_detectorMesh D.t)
    D.t (2*D.t) D.t D.t hd hd' hδ hδ' hq hq' D.epsilon_pos.le D.eps_pos.le D.t_pos.le
    (weighted_detectorMesh_pos D.t_pos).le (weighted_detectorMesh_le D.t_pos)
    D.t_pos.le le_rfl (mul_nonneg (by norm_num) D.t_pos.le) le_rfl
    D.t_pos.le le_rfl D.t_pos.le le_rfl
  have hn : 0 ≤ D.eps*(D.N:ℝ) := mul_nonneg D.eps_pos.le (Nat.cast_nonneg _)
  nlinarith only [hl,hn,D.e_pos,D.epsilon_pos,D.eps_pos,D.t_pos]

/-- Exact conversion of the physical source packet exponent.  This includes
the scalar and frequency factors, the original amplitude count, the annular
capacity shift, and restoration of the main upper-bin slack. -/
theorem weighted_source_packet_exponent (d δ q ε eps t mesh : ℝ)
    (hd : d≠0) (hδ : δ≠0) :
    -ly/2-(4/25)*ell+(3+17/25)*t+t*ell+
      d*(2*eps+t+q*(ell/d)-q*((2*(ly/d)-1)/(9/2)-4*t/9)/2+
        (3*(rowCount δ (q/δ)+159*ε+9*t)+1+2*t)/4+
        δ*mesh/4+δ*t/4-17/50)=
      numeratorExponent d δ (q/δ)+
        weightedSourceLoss d δ q ε eps t mesh t (2*t) t t := by
  unfold numeratorExponent weightedSourceLoss
  have hq : δ*(q/δ)=q := by field_simp
  rw [hq]
  unfold kappa
  field_simp
  <;> ring

/-- A common loss may be used when summing different error and amplitude
classes, without retaining their individual masked means. -/
theorem weighted_source_uniform_packet_budget {Δ : ℝ} (D : HighParameters.HighData Δ) :
    16*D.e+(120*D.ε+2*D.eps+13*D.t)+D.t ≤ 1/40000 := by
  apply OAI.SevenEighths.WeightedHighFinalAssembly.weighted_source_fixed_budget
  have hn : 0 ≤ D.eps*(D.N:ℝ) := mul_nonneg D.eps_pos.le (Nat.cast_nonneg _)
  nlinarith only [hn,D.e_pos,D.epsilon_pos,D.eps_pos,D.t_pos]

/-- The pointwise certificate before absorbing the fixed external height
degree.  Its right side is independent of the error mask and amplitude bin. -/
theorem weighted_source_packet_certificate {Δ : ℝ} (D : HighParameters.HighData Δ)
    (d a q : ℝ) (hd : 1/2 ≤ d) (hd' : d ≤ h+rowExtension)
    (ha : 1/3 ≤ 2*a-1) (ha' : a ≤ 7/8)
    (hq : 0 ≤ q) (hq' : q ≤ (2*a-1)/2) :
    numeratorExponent d (2*a-1) (q/(2*a-1))+
      weightedSourceLoss d (2*a-1) q D.ε D.eps D.t
        (weighted_detectorMesh D.t) D.t (2*D.t) D.t D.t ≤
      signal theta-1/40000-
        OAI.SevenEighths.WeightedHighFinalAssembly.weightedSourceSZExponent a D.e-D.t := by
  have hδ : 0 < 2*a-1 := by linarith
  have hdt : d ≤ 1 := by norm_num [h,rowExtension] at hd';linarith
  have hbudget := weighted_source_packet_fixed_budget D d (2*a-1) q
    (by linarith) hdt hδ.le (by linarith) hq hq'
  have hb := OAI.SevenEighths.WeightedHighFinalAssembly.weighted_source_integrated_certificate D
    d a (q/(2*a-1))
    (weightedSourceLoss d (2*a-1) q D.ε D.eps D.t (weighted_detectorMesh D.t)
      D.t (2*D.t) D.t D.t)
    hd' ha ha' (div_nonneg hq hδ.le) ((div_le_iff₀ hδ).mpr (by linarith)) hbudget
  linarith only [hb]

end WeightedQRH
end
