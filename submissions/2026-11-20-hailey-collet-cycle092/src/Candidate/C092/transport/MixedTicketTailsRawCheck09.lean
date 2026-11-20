/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group09_raw0 : ((group09.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group09_raw1 : ((group09.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group09_raw2 : ((group09.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group09_raw3 : ((group09.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group09_raw4 : ((group09.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group09_raw5 : ((group09.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group09_raw6 : ((group09.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group09_raw_checked : group09.all rawBridgeCheck=true := by
  have he : group09 = ((group09.drop 0).take 50) ++ ((group09.drop 50).take 50) ++ ((group09.drop 100).take 50) ++ ((group09.drop 150).take 50) ++ ((group09.drop 200).take 50) ++ ((group09.drop 250).take 50) ++ ((group09.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group09_raw0,group09_raw1,group09_raw2,group09_raw3,group09_raw4,group09_raw5,group09_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
