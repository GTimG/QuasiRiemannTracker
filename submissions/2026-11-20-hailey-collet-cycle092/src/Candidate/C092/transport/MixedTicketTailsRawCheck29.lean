/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group29_raw0 : ((group29.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group29_raw1 : ((group29.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group29_raw2 : ((group29.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group29_raw3 : ((group29.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group29_raw4 : ((group29.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group29_raw5 : ((group29.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group29_raw6 : ((group29.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group29_raw_checked : group29.all rawBridgeCheck=true := by
  have he : group29 = ((group29.drop 0).take 50) ++ ((group29.drop 50).take 50) ++ ((group29.drop 100).take 50) ++ ((group29.drop 150).take 50) ++ ((group29.drop 200).take 50) ++ ((group29.drop 250).take 50) ++ ((group29.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group29_raw0,group29_raw1,group29_raw2,group29_raw3,group29_raw4,group29_raw5,group29_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
