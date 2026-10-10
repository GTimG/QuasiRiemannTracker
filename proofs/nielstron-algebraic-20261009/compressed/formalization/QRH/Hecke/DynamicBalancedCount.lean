import QRH.Hecke.DynamicCountOptimization

namespace OAI.SevenEighths.QRHDetectorRowCount
noncomputable section

lemma balanced_count_identity {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    max (shortExponent δ x (QRH.Certificate.witness δ x))
      (longExponent δ (QRH.Certificate.witness δ x)) = QRH.adaptiveCount δ x := by
  have hj := QRH.Certificate.denominator_bounds hδ hδ' hx hx'
  have hd := QRH.Certificate.DP_bounds hx hx'
  have hj0 : QRH.Certificate.J δ x ≠ 0 := ne_of_gt (by linarith [hj.1])
  have hd0 : QRH.Certificate.D x ≠ 0 := ne_of_gt (by linarith [hd.1,hd.2.1])
  obtain ⟨hl,hs⟩ := QRH.Certificate.balanced_counts (δ:=δ) (x:=x) hj0 hd0
  change max (1-δ+δ*QRH.Certificate.P x/QRH.Certificate.D x*(3/2-QRH.Certificate.witness δ x))
    (1-δ+(5/6-δ)*(QRH.Certificate.witness δ x-1)) = _
  rw [hl,hs,max_self]

end
end OAI.SevenEighths.QRHDetectorRowCount
