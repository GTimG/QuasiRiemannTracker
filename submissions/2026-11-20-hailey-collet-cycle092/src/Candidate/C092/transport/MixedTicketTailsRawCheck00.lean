/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group00_raw0 : ((group00.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group00_raw1 : ((group00.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group00_raw2 : ((group00.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group00_raw3 : ((group00.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group00_raw4 : ((group00.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group00_raw5 : ((group00.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group00_raw6 : ((group00.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group00_raw_checked : group00.all rawBridgeCheck=true := by
  have he : group00 = ((group00.drop 0).take 50) ++ ((group00.drop 50).take 50) ++ ((group00.drop 100).take 50) ++ ((group00.drop 150).take 50) ++ ((group00.drop 200).take 50) ++ ((group00.drop 250).take 50) ++ ((group00.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group00_raw0,group00_raw1,group00_raw2,group00_raw3,group00_raw4,group00_raw5,group00_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
