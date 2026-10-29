/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00001_00032
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00033_00064
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00065_00096
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00097_00128
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00129_00160
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00161_00192
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00193_00224
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00225_00256
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00257_00288
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00289_00320
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00321_00352
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00353_00384
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00385_00416
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00417_00448
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00449_00480
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00481_00512
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00513_00544
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00545_00576
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00577_00608
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00609_00640
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00641_00672
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00673_00704
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00705_00736
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00737_00768
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00769_00800
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00801_00832
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00833_00864
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00865_00896
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00897_00928
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00929_00960
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00961_00992
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First00993_01024
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01025_01056
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01057_01088
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01089_01120
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01121_01152
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01153_01184
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01185_01216
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01217_01248
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01249_01280
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01281_01312
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01313_01344
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01345_01376
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01377_01408
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01409_01440
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01441_01472
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01473_01504
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01505_01536
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01537_01568
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01569_01600
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01601_01632
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01633_01664
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01665_01696
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First01697_01703
namespace Qrh.JointDetector.RestartSourceChains.First
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths QRH.Record1252270103Source

theorem source00411 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (99251525155089/100000000000000:ℝ) (1180870970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.prefix00411 hcores hβ h384
 exact h416

theorem source00608 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (24685443232821/25000000000000:ℝ) (1131620970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 exact h608

theorem source00734 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (98368350440523/100000000000000:ℝ) (1100120970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 have h640 := First00609_00640.source hcores hβ h608
 have h672 := First00641_00672.source hcores hβ h640
 have h704 := First00673_00704.source hcores hβ h672
 have h736 := First00705_00736.prefix00734 hcores hβ h704
 exact h736

theorem source00764 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (98274226585809/100000000000000:ℝ) (1092620970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 have h640 := First00609_00640.source hcores hβ h608
 have h672 := First00641_00672.source hcores hβ h640
 have h704 := First00673_00704.source hcores hβ h672
 have h736 := First00705_00736.source hcores hβ h704
 have h768 := First00737_00768.prefix00764 hcores hβ h736
 exact h768

theorem source00934 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (48852168020443/50000000000000:ℝ) (1050120970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 have h640 := First00609_00640.source hcores hβ h608
 have h672 := First00641_00672.source hcores hβ h640
 have h704 := First00673_00704.source hcores hβ h672
 have h736 := First00705_00736.source hcores hβ h704
 have h768 := First00737_00768.source hcores hβ h736
 have h800 := First00769_00800.source hcores hβ h768
 have h832 := First00801_00832.source hcores hβ h800
 have h864 := First00833_00864.source hcores hβ h832
 have h896 := First00865_00896.source hcores hβ h864
 have h928 := First00897_00928.source hcores hβ h896
 have h960 := First00929_00960.prefix00934 hcores hβ h928
 exact h960

theorem source01134 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (48478748967367/50000000000000:ℝ) (1000120970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 have h640 := First00609_00640.source hcores hβ h608
 have h672 := First00641_00672.source hcores hβ h640
 have h704 := First00673_00704.source hcores hβ h672
 have h736 := First00705_00736.source hcores hβ h704
 have h768 := First00737_00768.source hcores hβ h736
 have h800 := First00769_00800.source hcores hβ h768
 have h832 := First00801_00832.source hcores hβ h800
 have h864 := First00833_00864.source hcores hβ h832
 have h896 := First00865_00896.source hcores hβ h864
 have h928 := First00897_00928.source hcores hβ h896
 have h960 := First00929_00960.source hcores hβ h928
 have h992 := First00961_00992.source hcores hβ h960
 have h1024 := First00993_01024.source hcores hβ h992
 have h1056 := First01025_01056.source hcores hβ h1024
 have h1088 := First01057_01088.source hcores hβ h1056
 have h1120 := First01089_01120.source hcores hβ h1088
 have h1152 := First01121_01152.prefix01134 hcores hβ h1120
 exact h1152

theorem source01334 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (96132504200737/100000000000000:ℝ) (950120970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 have h640 := First00609_00640.source hcores hβ h608
 have h672 := First00641_00672.source hcores hβ h640
 have h704 := First00673_00704.source hcores hβ h672
 have h736 := First00705_00736.source hcores hβ h704
 have h768 := First00737_00768.source hcores hβ h736
 have h800 := First00769_00800.source hcores hβ h768
 have h832 := First00801_00832.source hcores hβ h800
 have h864 := First00833_00864.source hcores hβ h832
 have h896 := First00865_00896.source hcores hβ h864
 have h928 := First00897_00928.source hcores hβ h896
 have h960 := First00929_00960.source hcores hβ h928
 have h992 := First00961_00992.source hcores hβ h960
 have h1024 := First00993_01024.source hcores hβ h992
 have h1056 := First01025_01056.source hcores hβ h1024
 have h1088 := First01057_01088.source hcores hβ h1056
 have h1120 := First01089_01120.source hcores hβ h1088
 have h1152 := First01121_01152.source hcores hβ h1120
 have h1184 := First01153_01184.source hcores hβ h1152
 have h1216 := First01185_01216.source hcores hβ h1184
 have h1248 := First01217_01248.source hcores hβ h1216
 have h1280 := First01249_01280.source hcores hβ h1248
 have h1312 := First01281_01312.source hcores hβ h1280
 have h1344 := First01313_01344.prefix01334 hcores hβ h1312
 exact h1344

theorem source01434 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (95694034153033/100000000000000:ℝ) (925120970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 have h640 := First00609_00640.source hcores hβ h608
 have h672 := First00641_00672.source hcores hβ h640
 have h704 := First00673_00704.source hcores hβ h672
 have h736 := First00705_00736.source hcores hβ h704
 have h768 := First00737_00768.source hcores hβ h736
 have h800 := First00769_00800.source hcores hβ h768
 have h832 := First00801_00832.source hcores hβ h800
 have h864 := First00833_00864.source hcores hβ h832
 have h896 := First00865_00896.source hcores hβ h864
 have h928 := First00897_00928.source hcores hβ h896
 have h960 := First00929_00960.source hcores hβ h928
 have h992 := First00961_00992.source hcores hβ h960
 have h1024 := First00993_01024.source hcores hβ h992
 have h1056 := First01025_01056.source hcores hβ h1024
 have h1088 := First01057_01088.source hcores hβ h1056
 have h1120 := First01089_01120.source hcores hβ h1088
 have h1152 := First01121_01152.source hcores hβ h1120
 have h1184 := First01153_01184.source hcores hβ h1152
 have h1216 := First01185_01216.source hcores hβ h1184
 have h1248 := First01217_01248.source hcores hβ h1216
 have h1280 := First01249_01280.source hcores hβ h1248
 have h1312 := First01281_01312.source hcores hβ h1280
 have h1344 := First01313_01344.source hcores hβ h1312
 have h1376 := First01345_01376.source hcores hβ h1344
 have h1408 := First01377_01408.source hcores hβ h1376
 have h1440 := First01409_01440.prefix01434 hcores hβ h1408
 exact h1440

theorem source01534 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (95239424367701/100000000000000:ℝ) (900120970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 have h640 := First00609_00640.source hcores hβ h608
 have h672 := First00641_00672.source hcores hβ h640
 have h704 := First00673_00704.source hcores hβ h672
 have h736 := First00705_00736.source hcores hβ h704
 have h768 := First00737_00768.source hcores hβ h736
 have h800 := First00769_00800.source hcores hβ h768
 have h832 := First00801_00832.source hcores hβ h800
 have h864 := First00833_00864.source hcores hβ h832
 have h896 := First00865_00896.source hcores hβ h864
 have h928 := First00897_00928.source hcores hβ h896
 have h960 := First00929_00960.source hcores hβ h928
 have h992 := First00961_00992.source hcores hβ h960
 have h1024 := First00993_01024.source hcores hβ h992
 have h1056 := First01025_01056.source hcores hβ h1024
 have h1088 := First01057_01088.source hcores hβ h1056
 have h1120 := First01089_01120.source hcores hβ h1088
 have h1152 := First01121_01152.source hcores hβ h1120
 have h1184 := First01153_01184.source hcores hβ h1152
 have h1216 := First01185_01216.source hcores hβ h1184
 have h1248 := First01217_01248.source hcores hβ h1216
 have h1280 := First01249_01280.source hcores hβ h1248
 have h1312 := First01281_01312.source hcores hβ h1280
 have h1344 := First01313_01344.source hcores hβ h1312
 have h1376 := First01345_01376.source hcores hβ h1344
 have h1408 := First01377_01408.source hcores hβ h1376
 have h1440 := First01409_01440.source hcores hβ h1408
 have h1472 := First01441_01472.source hcores hβ h1440
 have h1504 := First01473_01504.source hcores hβ h1472
 have h1536 := First01505_01536.prefix01534 hcores hβ h1504
 exact h1536

theorem source01634 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (94768797030979/100000000000000:ℝ) (875120970349/500000000000:ℝ) (1/10:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 have h640 := First00609_00640.source hcores hβ h608
 have h672 := First00641_00672.source hcores hβ h640
 have h704 := First00673_00704.source hcores hβ h672
 have h736 := First00705_00736.source hcores hβ h704
 have h768 := First00737_00768.source hcores hβ h736
 have h800 := First00769_00800.source hcores hβ h768
 have h832 := First00801_00832.source hcores hβ h800
 have h864 := First00833_00864.source hcores hβ h832
 have h896 := First00865_00896.source hcores hβ h864
 have h928 := First00897_00928.source hcores hβ h896
 have h960 := First00929_00960.source hcores hβ h928
 have h992 := First00961_00992.source hcores hβ h960
 have h1024 := First00993_01024.source hcores hβ h992
 have h1056 := First01025_01056.source hcores hβ h1024
 have h1088 := First01057_01088.source hcores hβ h1056
 have h1120 := First01089_01120.source hcores hβ h1088
 have h1152 := First01121_01152.source hcores hβ h1120
 have h1184 := First01153_01184.source hcores hβ h1152
 have h1216 := First01185_01216.source hcores hβ h1184
 have h1248 := First01217_01248.source hcores hβ h1216
 have h1280 := First01249_01280.source hcores hβ h1248
 have h1312 := First01281_01312.source hcores hβ h1280
 have h1344 := First01313_01344.source hcores hβ h1312
 have h1376 := First01345_01376.source hcores hβ h1344
 have h1408 := First01377_01408.source hcores hβ h1376
 have h1440 := First01409_01440.source hcores hβ h1408
 have h1472 := First01441_01472.source hcores hβ h1440
 have h1504 := First01473_01504.source hcores hβ h1472
 have h1536 := First01505_01536.source hcores hβ h1504
 have h1568 := First01537_01568.source hcores hβ h1536
 have h1600 := First01569_01600.source hcores hβ h1568
 have h1632 := First01601_01632.source hcores hβ h1600
 have h1664 := First01633_01664.prefix01634 hcores hβ h1632
 exact h1664

theorem source01703 (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : GlobalSource (2360868829489/2500000000000:ℝ) (857870970349/500000000000:ℝ) (101/1000:ℝ) := by
 have h32 := First00001_00032.source hcores hβ hp
 have h64 := First00033_00064.source hcores hβ h32
 have h96 := First00065_00096.source hcores hβ h64
 have h128 := First00097_00128.source hcores hβ h96
 have h160 := First00129_00160.source hcores hβ h128
 have h192 := First00161_00192.source hcores hβ h160
 have h224 := First00193_00224.source hcores hβ h192
 have h256 := First00225_00256.source hcores hβ h224
 have h288 := First00257_00288.source hcores hβ h256
 have h320 := First00289_00320.source hcores hβ h288
 have h352 := First00321_00352.source hcores hβ h320
 have h384 := First00353_00384.source hcores hβ h352
 have h416 := First00385_00416.source hcores hβ h384
 have h448 := First00417_00448.source hcores hβ h416
 have h480 := First00449_00480.source hcores hβ h448
 have h512 := First00481_00512.source hcores hβ h480
 have h544 := First00513_00544.source hcores hβ h512
 have h576 := First00545_00576.source hcores hβ h544
 have h608 := First00577_00608.source hcores hβ h576
 have h640 := First00609_00640.source hcores hβ h608
 have h672 := First00641_00672.source hcores hβ h640
 have h704 := First00673_00704.source hcores hβ h672
 have h736 := First00705_00736.source hcores hβ h704
 have h768 := First00737_00768.source hcores hβ h736
 have h800 := First00769_00800.source hcores hβ h768
 have h832 := First00801_00832.source hcores hβ h800
 have h864 := First00833_00864.source hcores hβ h832
 have h896 := First00865_00896.source hcores hβ h864
 have h928 := First00897_00928.source hcores hβ h896
 have h960 := First00929_00960.source hcores hβ h928
 have h992 := First00961_00992.source hcores hβ h960
 have h1024 := First00993_01024.source hcores hβ h992
 have h1056 := First01025_01056.source hcores hβ h1024
 have h1088 := First01057_01088.source hcores hβ h1056
 have h1120 := First01089_01120.source hcores hβ h1088
 have h1152 := First01121_01152.source hcores hβ h1120
 have h1184 := First01153_01184.source hcores hβ h1152
 have h1216 := First01185_01216.source hcores hβ h1184
 have h1248 := First01217_01248.source hcores hβ h1216
 have h1280 := First01249_01280.source hcores hβ h1248
 have h1312 := First01281_01312.source hcores hβ h1280
 have h1344 := First01313_01344.source hcores hβ h1312
 have h1376 := First01345_01376.source hcores hβ h1344
 have h1408 := First01377_01408.source hcores hβ h1376
 have h1440 := First01409_01440.source hcores hβ h1408
 have h1472 := First01441_01472.source hcores hβ h1440
 have h1504 := First01473_01504.source hcores hβ h1472
 have h1536 := First01505_01536.source hcores hβ h1504
 have h1568 := First01537_01568.source hcores hβ h1536
 have h1600 := First01569_01600.source hcores hβ h1568
 have h1632 := First01601_01632.source hcores hβ h1600
 have h1664 := First01633_01664.source hcores hβ h1632
 have h1696 := First01665_01696.source hcores hβ h1664
 have h1703 := First01697_01703.source hcores hβ h1696
 exact h1703

end
end Qrh.JointDetector.RestartSourceChains.First
