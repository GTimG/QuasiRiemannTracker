/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.ContactCertificate

/-!
# Exact bindings to the recovered Q receipt

This file is generated from the original receipt by
`scripts/generate_contact_receipt.py`. Each literal interval is proved equal to
the interval computed by the sound contact expression evaluator.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace QRH.ContactCertificate

/-- Literal directed g0 endpoints in the recovered Q receipt. -/
def g0Receipt : QRH.RationalInterval.Interval :=
  ⟨(11596203021434442605747750453616727403725294849723975122231193313956010428057908767320160466192853715222739674442396014996421385794981458761874143123656235 / 199730949502598473383284419258556504342073419898432270469479168929750666568379535609779846127643773512530895319567690517262805569559882985947376542377418777),
   (5435720166297394971461256489034116698799740361636644804955971984318009023280238946105606142710026378687456313458040147179099095563577660225312312866000705 / 93623882579343034398398712285557430924511928999774531058820591820834493335275635311478037062103120633059145932331106851290007404221522938938187836841198731)⟩

/-- Both literal g0 endpoints equal the independently evaluated exact interval. -/
theorem g0_receipt_eq : g0Receipt = g0Interval := by
  decide +kernel

/-- The receipt interval encloses the actual real contact coefficient. -/
theorem g0_receipt_sound {x : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval x) :
    QRH.RationalInterval.Contains g0Receipt (g0 (wValue x)) := by
  rw [g0_receipt_eq]
  exact g0_enclosed hx

/-- Literal directed g1 endpoints in the recovered Q receipt. -/
def g1Receipt : QRH.RationalInterval.Interval :=
  ⟨(11702109555380945979458158757736572920063891944649354350795306279667235067844192995503881 / 153982855531089011381834261407101670667124365225244854997433077402349934171513784340805446),
   (11702109555380945979489918655082810857366312919752168470718941908329469442844192995503881 / 153982855531089011381809789007591609746245709397672981497193695866385559171513784340805446)⟩

/-- Both literal g1 endpoints equal the independently evaluated exact interval. -/
theorem g1_receipt_eq : g1Receipt = g1Interval := by
  decide +kernel

/-- The receipt interval encloses the actual real contact coefficient. -/
theorem g1_receipt_sound {x : ℝ}
    (hx : QRH.RationalInterval.Contains alphaInterval x) :
    QRH.RationalInterval.Contains g1Receipt (g1 (wValue x)) := by
  rw [g1_receipt_eq]
  exact g1_enclosed hx

end QRH.ContactCertificate
