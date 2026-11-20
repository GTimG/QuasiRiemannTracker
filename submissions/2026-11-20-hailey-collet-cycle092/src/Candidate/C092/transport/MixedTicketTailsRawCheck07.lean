/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group07_raw0 : ((group07.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group07_raw1 : ((group07.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group07_raw2 : ((group07.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group07_raw3 : ((group07.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group07_raw4 : ((group07.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group07_raw5 : ((group07.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group07_raw6 : ((group07.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group07_raw_checked : group07.all rawBridgeCheck=true := by
  have he : group07 = ((group07.drop 0).take 50) ++ ((group07.drop 50).take 50) ++ ((group07.drop 100).take 50) ++ ((group07.drop 150).take 50) ++ ((group07.drop 200).take 50) ++ ((group07.drop 250).take 50) ++ ((group07.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group07_raw0,group07_raw1,group07_raw2,group07_raw3,group07_raw4,group07_raw5,group07_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
