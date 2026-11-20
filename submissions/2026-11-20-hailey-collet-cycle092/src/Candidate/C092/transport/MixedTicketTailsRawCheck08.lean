/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedTicketTailsRawCore
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QRH.Cycle092.MixedTicketTails
open QRH.Cycle092.TopData
theorem group08_raw0 : ((group08.drop 0).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group08_raw1 : ((group08.drop 50).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group08_raw2 : ((group08.drop 100).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group08_raw3 : ((group08.drop 150).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group08_raw4 : ((group08.drop 200).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group08_raw5 : ((group08.drop 250).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group08_raw6 : ((group08.drop 300).take 50).all rawBridgeCheck=true := by decide +kernel
theorem group08_raw_checked : group08.all rawBridgeCheck=true := by
  have he : group08 = ((group08.drop 0).take 50) ++ ((group08.drop 50).take 50) ++ ((group08.drop 100).take 50) ++ ((group08.drop 150).take 50) ++ ((group08.drop 200).take 50) ++ ((group08.drop 250).take 50) ++ ((group08.drop 300).take 50) := by rfl
  rw [he]
  simp only [List.all_append,group08_raw0,group08_raw1,group08_raw2,group08_raw3,group08_raw4,group08_raw5,group08_raw6,Bool.and_self]
end QRH.Cycle092.MixedTicketTails
