/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group15_raw0 : ((group15.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group15_raw1 : ((group15.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group15_raw2 : ((group15.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group15_raw3 : ((group15.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group15_raw4 : ((group15.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group15_raw5 : ((group15.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group15_raw6 : ((group15.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group15_raw_checked : group15.all rawBridgeCheck=true := by
  have he : group15 = ((group15.drop 0).take 50) ++ ((group15.drop 50).take 50) ++ ((group15.drop 100).take 50) ++ ((group15.drop 150).take 50) ++ ((group15.drop 200).take 50) ++ ((group15.drop 250).take 50) ++ ((group15.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group15_raw0,group15_raw1,group15_raw2,group15_raw3,group15_raw4,group15_raw5,group15_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
