import Candidate.Target836.Detector836.Region
import Candidate.Affine.Balanced

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
