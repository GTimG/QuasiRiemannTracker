/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group18_raw0 : ((group18.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group18_raw1 : ((group18.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group18_raw2 : ((group18.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group18_raw3 : ((group18.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group18_raw4 : ((group18.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group18_raw5 : ((group18.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group18_raw6 : ((group18.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group18_raw_checked : group18.all rawBridgeCheck=true := by
  have he : group18 = ((group18.drop 0).take 50) ++ ((group18.drop 50).take 50) ++ ((group18.drop 100).take 50) ++ ((group18.drop 150).take 50) ++ ((group18.drop 200).take 50) ++ ((group18.drop 250).take 50) ++ ((group18.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group18_raw0,group18_raw1,group18_raw2,group18_raw3,group18_raw4,group18_raw5,group18_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
