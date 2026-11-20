/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group26_raw0 : ((group26.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group26_raw1 : ((group26.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group26_raw2 : ((group26.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group26_raw3 : ((group26.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group26_raw4 : ((group26.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group26_raw5 : ((group26.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group26_raw6 : ((group26.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group26_raw_checked : group26.all rawBridgeCheck=true := by
  have he : group26 = ((group26.drop 0).take 50) ++ ((group26.drop 50).take 50) ++ ((group26.drop 100).take 50) ++ ((group26.drop 150).take 50) ++ ((group26.drop 200).take 50) ++ ((group26.drop 250).take 50) ++ ((group26.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group26_raw0,group26_raw1,group26_raw2,group26_raw3,group26_raw4,group26_raw5,group26_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
