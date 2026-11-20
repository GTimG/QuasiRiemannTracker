/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group22_raw0 : ((group22.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group22_raw1 : ((group22.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group22_raw2 : ((group22.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group22_raw3 : ((group22.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group22_raw4 : ((group22.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group22_raw5 : ((group22.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group22_raw6 : ((group22.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group22_raw_checked : group22.all rawBridgeCheck=true := by
  have he : group22 = ((group22.drop 0).take 50) ++ ((group22.drop 50).take 50) ++ ((group22.drop 100).take 50) ++ ((group22.drop 150).take 50) ++ ((group22.drop 200).take 50) ++ ((group22.drop 250).take 50) ++ ((group22.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group22_raw0,group22_raw1,group22_raw2,group22_raw3,group22_raw4,group22_raw5,group22_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
