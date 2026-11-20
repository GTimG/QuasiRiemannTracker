/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group27_raw0 : ((group27.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group27_raw1 : ((group27.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group27_raw2 : ((group27.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group27_raw3 : ((group27.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group27_raw4 : ((group27.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group27_raw5 : ((group27.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group27_raw6 : ((group27.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group27_raw_checked : group27.all rawBridgeCheck=true := by
  have he : group27 = ((group27.drop 0).take 50) ++ ((group27.drop 50).take 50) ++ ((group27.drop 100).take 50) ++ ((group27.drop 150).take 50) ++ ((group27.drop 200).take 50) ++ ((group27.drop 250).take 50) ++ ((group27.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group27_raw0,group27_raw1,group27_raw2,group27_raw3,group27_raw4,group27_raw5,group27_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
