/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group20_raw0 : ((group20.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group20_raw1 : ((group20.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group20_raw2 : ((group20.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group20_raw3 : ((group20.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group20_raw4 : ((group20.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group20_raw5 : ((group20.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group20_raw6 : ((group20.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group20_raw_checked : group20.all rawBridgeCheck=true := by
  have he : group20 = ((group20.drop 0).take 50) ++ ((group20.drop 50).take 50) ++ ((group20.drop 100).take 50) ++ ((group20.drop 150).take 50) ++ ((group20.drop 200).take 50) ++ ((group20.drop 250).take 50) ++ ((group20.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group20_raw0,group20_raw1,group20_raw2,group20_raw3,group20_raw4,group20_raw5,group20_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
