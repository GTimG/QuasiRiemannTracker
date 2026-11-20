/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group24_raw0 : ((group24.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group24_raw1 : ((group24.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group24_raw2 : ((group24.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group24_raw3 : ((group24.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group24_raw4 : ((group24.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group24_raw5 : ((group24.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group24_raw6 : ((group24.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group24_raw_checked : group24.all rawBridgeCheck=true := by
  have he : group24 = ((group24.drop 0).take 50) ++ ((group24.drop 50).take 50) ++ ((group24.drop 100).take 50) ++ ((group24.drop 150).take 50) ++ ((group24.drop 200).take 50) ++ ((group24.drop 250).take 50) ++ ((group24.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group24_raw0,group24_raw1,group24_raw2,group24_raw3,group24_raw4,group24_raw5,group24_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
