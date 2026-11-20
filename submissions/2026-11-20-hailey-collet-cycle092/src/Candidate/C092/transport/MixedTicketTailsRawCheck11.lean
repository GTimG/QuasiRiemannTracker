/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group11_raw0 : ((group11.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group11_raw1 : ((group11.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group11_raw2 : ((group11.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group11_raw3 : ((group11.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group11_raw4 : ((group11.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group11_raw5 : ((group11.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group11_raw6 : ((group11.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group11_raw_checked : group11.all rawBridgeCheck=true := by
  have he : group11 = ((group11.drop 0).take 50) ++ ((group11.drop 50).take 50) ++ ((group11.drop 100).take 50) ++ ((group11.drop 150).take 50) ++ ((group11.drop 200).take 50) ++ ((group11.drop 250).take 50) ++ ((group11.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group11_raw0,group11_raw1,group11_raw2,group11_raw3,group11_raw4,group11_raw5,group11_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
