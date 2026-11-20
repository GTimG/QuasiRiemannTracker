/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group03_raw0 : ((group03.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group03_raw1 : ((group03.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group03_raw2 : ((group03.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group03_raw3 : ((group03.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group03_raw4 : ((group03.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group03_raw5 : ((group03.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group03_raw6 : ((group03.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group03_raw_checked : group03.all rawBridgeCheck=true := by
  have he : group03 = ((group03.drop 0).take 50) ++ ((group03.drop 50).take 50) ++ ((group03.drop 100).take 50) ++ ((group03.drop 150).take 50) ++ ((group03.drop 200).take 50) ++ ((group03.drop 250).take 50) ++ ((group03.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group03_raw0,group03_raw1,group03_raw2,group03_raw3,group03_raw4,group03_raw5,group03_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
