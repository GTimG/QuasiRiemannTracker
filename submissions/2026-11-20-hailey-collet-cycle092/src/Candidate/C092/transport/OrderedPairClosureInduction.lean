/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine independent-pair source on the full earlier ordered prefix. -/
import Candidate.C092.transport.StrongPairInduction
import Candidate.C092.transport.StrongPairOriginal
import Candidate.C092.transport.LowActualOrderedCover

set_option autoImplicit false
namespace QRH.Cycle092.OrderedPairClosure
noncomputable section
open QRH.Cycle092.StrongPair QRH.Cycle092.LowActual
open QRH.Cycle090 QRH.SourceCertificate

/-- The actual independent-pair induction uses the whole strictly earlier
closed prefix required by live radial rescaling, rather than an H-only pair.
Its 2904-stage descent and native start are genuine existing theorems. The
analytic increment remains explicit until supplied by the source assembly. -/
theorem all_pair_strips_of_full_increment
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (increment : ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      EarlierCover PairOpenWidth y → PairOpenWidth n y) :
    ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y → PairOpenWidth n y :=
  ordered_source_induction_cover PairOpenWidth
    (fun _ _ hy hy' hn hr l hl0 hl => native_pair_box hβ hy hy' hn hr hl0 hl) increment

/-- All componentwise shorter labelled caps retain the quota proved at the
original admitted pair. Actual lengths need not themselves be ordered. -/
theorem all_shortened_pair_quotas
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (increment : ∀ n y, sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      EarlierCover PairOpenWidth y → PairOpenWidth n y)
    {n y N Y l : ℝ} (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY)
    (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hN : N ≤ n) (hY : Y ≤ y) (hl0 : 0 ≤ l) (hl : l < sourceWidth n y) :
    PairUniformBox N Y l :=
  pair_uniform_mono hN hY le_rfl
    (all_pair_strips_of_full_increment hβ increment n y hy0 hy1 hn0 hn1 l hl0 hl)

#print axioms all_pair_strips_of_full_increment
#print axioms all_shortened_pair_quotas
end
end QRH.Cycle092.OrderedPairClosure
