/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group06_raw0 : ((group06.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group06_raw1 : ((group06.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group06_raw2 : ((group06.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group06_raw3 : ((group06.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group06_raw4 : ((group06.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group06_raw5 : ((group06.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group06_raw6 : ((group06.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group06_raw_checked : group06.all rawBridgeCheck=true := by
  have he : group06 = ((group06.drop 0).take 50) ++ ((group06.drop 50).take 50) ++ ((group06.drop 100).take 50) ++ ((group06.drop 150).take 50) ++ ((group06.drop 200).take 50) ++ ((group06.drop 250).take 50) ++ ((group06.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group06_raw0,group06_raw1,group06_raw2,group06_raw3,group06_raw4,group06_raw5,group06_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
