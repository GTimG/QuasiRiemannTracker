/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group16_raw0 : ((group16.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group16_raw1 : ((group16.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group16_raw2 : ((group16.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group16_raw3 : ((group16.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group16_raw4 : ((group16.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group16_raw5 : ((group16.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group16_raw6 : ((group16.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group16_raw_checked : group16.all rawBridgeCheck=true := by
  have he : group16 = ((group16.drop 0).take 50) ++ ((group16.drop 50).take 50) ++ ((group16.drop 100).take 50) ++ ((group16.drop 150).take 50) ++ ((group16.drop 200).take 50) ++ ((group16.drop 250).take 50) ++ ((group16.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group16_raw0,group16_raw1,group16_raw2,group16_raw3,group16_raw4,group16_raw5,group16_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
