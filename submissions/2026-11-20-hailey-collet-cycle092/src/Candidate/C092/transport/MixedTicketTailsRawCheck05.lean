/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group05_raw0 : ((group05.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group05_raw1 : ((group05.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group05_raw2 : ((group05.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group05_raw3 : ((group05.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group05_raw4 : ((group05.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group05_raw5 : ((group05.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group05_raw6 : ((group05.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group05_raw_checked : group05.all rawBridgeCheck=true := by
  have he : group05 = ((group05.drop 0).take 50) ++ ((group05.drop 50).take 50) ++ ((group05.drop 100).take 50) ++ ((group05.drop 150).take 50) ++ ((group05.drop 200).take 50) ++ ((group05.drop 250).take 50) ++ ((group05.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group05_raw0,group05_raw1,group05_raw2,group05_raw3,group05_raw4,group05_raw5,group05_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
