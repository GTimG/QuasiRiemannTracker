/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group01_raw0 : ((group01.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group01_raw1 : ((group01.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group01_raw2 : ((group01.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group01_raw3 : ((group01.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group01_raw4 : ((group01.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group01_raw5 : ((group01.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group01_raw6 : ((group01.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group01_raw_checked : group01.all rawBridgeCheck=true := by
  have he : group01 = ((group01.drop 0).take 50) ++ ((group01.drop 50).take 50) ++ ((group01.drop 100).take 50) ++ ((group01.drop 150).take 50) ++ ((group01.drop 200).take 50) ++ ((group01.drop 250).take 50) ++ ((group01.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group01_raw0,group01_raw1,group01_raw2,group01_raw3,group01_raw4,group01_raw5,group01_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
