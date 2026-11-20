/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group13_raw0 : ((group13.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group13_raw1 : ((group13.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group13_raw2 : ((group13.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group13_raw3 : ((group13.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group13_raw4 : ((group13.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group13_raw5 : ((group13.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group13_raw6 : ((group13.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group13_raw_checked : group13.all rawBridgeCheck=true := by
  have he : group13 = ((group13.drop 0).take 50) ++ ((group13.drop 50).take 50) ++ ((group13.drop 100).take 50) ++ ((group13.drop 150).take 50) ++ ((group13.drop 200).take 50) ++ ((group13.drop 250).take 50) ++ ((group13.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group13_raw0,group13_raw1,group13_raw2,group13_raw3,group13_raw4,group13_raw5,group13_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
