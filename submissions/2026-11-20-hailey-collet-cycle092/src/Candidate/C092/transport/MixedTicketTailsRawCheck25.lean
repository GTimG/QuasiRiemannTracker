/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group25_raw0 : ((group25.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group25_raw1 : ((group25.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group25_raw2 : ((group25.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group25_raw3 : ((group25.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group25_raw4 : ((group25.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group25_raw5 : ((group25.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group25_raw6 : ((group25.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group25_raw_checked : group25.all rawBridgeCheck=true := by
  have he : group25 = ((group25.drop 0).take 50) ++ ((group25.drop 50).take 50) ++ ((group25.drop 100).take 50) ++ ((group25.drop 150).take 50) ++ ((group25.drop 200).take 50) ++ ((group25.drop 250).take 50) ++ ((group25.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group25_raw0,group25_raw1,group25_raw2,group25_raw3,group25_raw4,group25_raw5,group25_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
