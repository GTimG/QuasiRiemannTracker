/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group21_raw0 : ((group21.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group21_raw1 : ((group21.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group21_raw2 : ((group21.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group21_raw3 : ((group21.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group21_raw4 : ((group21.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group21_raw5 : ((group21.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group21_raw6 : ((group21.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group21_raw_checked : group21.all rawBridgeCheck=true := by
  have he : group21 = ((group21.drop 0).take 50) ++ ((group21.drop 50).take 50) ++ ((group21.drop 100).take 50) ++ ((group21.drop 150).take 50) ++ ((group21.drop 200).take 50) ++ ((group21.drop 250).take 50) ++ ((group21.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group21_raw0,group21_raw1,group21_raw2,group21_raw3,group21_raw4,group21_raw5,group21_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
