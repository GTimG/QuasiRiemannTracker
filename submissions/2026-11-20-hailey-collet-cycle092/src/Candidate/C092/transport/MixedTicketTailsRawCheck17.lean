/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group17_raw0 : ((group17.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group17_raw1 : ((group17.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group17_raw2 : ((group17.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group17_raw3 : ((group17.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group17_raw4 : ((group17.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group17_raw5 : ((group17.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group17_raw6 : ((group17.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group17_raw_checked : group17.all rawBridgeCheck=true := by
  have he : group17 = ((group17.drop 0).take 50) ++ ((group17.drop 50).take 50) ++ ((group17.drop 100).take 50) ++ ((group17.drop 150).take 50) ++ ((group17.drop 200).take 50) ++ ((group17.drop 250).take 50) ++ ((group17.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group17_raw0,group17_raw1,group17_raw2,group17_raw3,group17_raw4,group17_raw5,group17_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
