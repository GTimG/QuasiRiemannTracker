/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group14_raw0 : ((group14.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group14_raw1 : ((group14.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group14_raw2 : ((group14.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group14_raw3 : ((group14.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group14_raw4 : ((group14.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group14_raw5 : ((group14.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group14_raw6 : ((group14.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group14_raw_checked : group14.all rawBridgeCheck=true := by
  have he : group14 = ((group14.drop 0).take 50) ++ ((group14.drop 50).take 50) ++ ((group14.drop 100).take 50) ++ ((group14.drop 150).take 50) ++ ((group14.drop 200).take 50) ++ ((group14.drop 250).take 50) ++ ((group14.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group14_raw0,group14_raw1,group14_raw2,group14_raw3,group14_raw4,group14_raw5,group14_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
