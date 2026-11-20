/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group10_raw0 : ((group10.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group10_raw1 : ((group10.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group10_raw2 : ((group10.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group10_raw3 : ((group10.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group10_raw4 : ((group10.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group10_raw5 : ((group10.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group10_raw6 : ((group10.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group10_raw_checked : group10.all rawBridgeCheck=true := by
  have he : group10 = ((group10.drop 0).take 50) ++ ((group10.drop 50).take 50) ++ ((group10.drop 100).take 50) ++ ((group10.drop 150).take 50) ++ ((group10.drop 200).take 50) ++ ((group10.drop 250).take 50) ++ ((group10.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group10_raw0,group10_raw1,group10_raw2,group10_raw3,group10_raw4,group10_raw5,group10_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
