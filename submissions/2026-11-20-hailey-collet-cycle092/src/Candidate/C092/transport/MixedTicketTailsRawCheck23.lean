/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group23_raw0 : ((group23.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group23_raw1 : ((group23.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group23_raw2 : ((group23.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group23_raw3 : ((group23.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group23_raw4 : ((group23.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group23_raw5 : ((group23.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group23_raw6 : ((group23.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group23_raw_checked : group23.all rawBridgeCheck=true := by
  have he : group23 = ((group23.drop 0).take 50) ++ ((group23.drop 50).take 50) ++ ((group23.drop 100).take 50) ++ ((group23.drop 150).take 50) ++ ((group23.drop 200).take 50) ++ ((group23.drop 250).take 50) ++ ((group23.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group23_raw0,group23_raw1,group23_raw2,group23_raw3,group23_raw4,group23_raw5,group23_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
