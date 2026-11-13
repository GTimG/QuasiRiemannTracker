/- Subhanjan Das; MIT for new assembly; AI-assisted with OpenAI Codex. -/
import Candidate.CoreBridge
import Candidate.Graphs.BCount000
import Candidate.Graphs.BCount001
import Candidate.Graphs.BCount002
import Candidate.Graphs.BCount003
import Candidate.Graphs.BCount004
import Candidate.Graphs.BCount005
import Candidate.Graphs.BCount006
import Candidate.Graphs.BCount007
import Candidate.Graphs.BCount008
import Candidate.Graphs.BCount009
import Candidate.Graphs.BCount010
import Candidate.Graphs.BCount011
import Candidate.Graphs.BCount012
import Candidate.Graphs.BCount013
import Candidate.Graphs.BCount014
import Candidate.Graphs.BCount015
import Candidate.Graphs.BCount016
import Candidate.Graphs.BCount017
import Candidate.Graphs.BCount018
import Candidate.Graphs.BCount019
import Candidate.Graphs.BCount020
import Candidate.Graphs.BCount021
import Candidate.Graphs.BCount022
import Candidate.Graphs.BCount023
import Candidate.Graphs.BCount024
import Candidate.Graphs.BCount025
import Candidate.Graphs.BCount026
import Candidate.Graphs.BCount027
import Candidate.Graphs.BCount028
import Candidate.Graphs.BCount029
import Candidate.Graphs.BCount030
import Candidate.Graphs.BCount031
import Candidate.Graphs.BCount032
import Candidate.Graphs.BCount033
import Candidate.Graphs.BCount034
import Candidate.Graphs.BCount035
import Candidate.Graphs.BCount036
import Candidate.Graphs.BCount037
import Candidate.Graphs.BCount038
import Candidate.Graphs.BCount039
import Candidate.Graphs.BCount040
import Candidate.Graphs.BCount041
import Candidate.Graphs.BCount042
import Candidate.Graphs.BCount043
import Candidate.Graphs.BCount044
import Candidate.Graphs.BCount045
import Candidate.Graphs.BCount046
import Candidate.Graphs.BCount047
import Candidate.Graphs.BCount048
import Candidate.Graphs.BCount049
import Candidate.Graphs.BCount050
import Candidate.Graphs.BCount051
import Candidate.Graphs.BCount052
import Candidate.Graphs.BCount053
import Candidate.Graphs.BCount054
import Candidate.Graphs.BCount055
import Candidate.Graphs.BCount056
import Candidate.Graphs.BCount057
import Candidate.Graphs.BCount058
import Candidate.Graphs.BCount059
import Candidate.Graphs.BCount060
import Candidate.Graphs.BCount061
import Candidate.Graphs.BCount062
import Candidate.Graphs.BCount063
import Candidate.Graphs.BCount064
import Candidate.Graphs.BCount065
import Candidate.Graphs.BCount066
import Candidate.Graphs.BCount067
import Candidate.Graphs.BCount068
import Candidate.Graphs.BCount069
import Candidate.Graphs.BCount070
import Candidate.Graphs.BCount071
import Candidate.Graphs.BCount072
import Candidate.Graphs.BCount073
import Candidate.Graphs.BCount074
import Candidate.Graphs.BCount075
import Candidate.Graphs.BCount076
import Candidate.Graphs.BCount077
import Candidate.Graphs.BCount078
import Candidate.Graphs.BCount079
import Candidate.Graphs.BCount080
import Candidate.Graphs.BCount081
import Candidate.Graphs.BCount082
import Candidate.Graphs.BCount083
import Candidate.Graphs.BCount084
import Candidate.Graphs.BCount085
import Candidate.Graphs.BCount086
import Candidate.Graphs.BCount087
import Candidate.Graphs.BCount088
import Candidate.Graphs.BCount089
import Candidate.Graphs.BCount090
import Candidate.Graphs.BCount091
import Candidate.Graphs.BCount092
import Candidate.Graphs.BCount093
import Candidate.Graphs.BCount094
import Candidate.Graphs.BCount095
import Candidate.Graphs.BCount096
import Candidate.Graphs.BCount097
import Candidate.Graphs.BCount098
import Candidate.Graphs.BCount099
import Candidate.Graphs.BCount100
import Candidate.Graphs.BCount101
import Candidate.Graphs.BCount102
import Candidate.Graphs.BCount103
import Candidate.Graphs.BCount104
import Candidate.Graphs.BCount105
import Candidate.Graphs.BCount106
import Candidate.Graphs.BCount107
import Candidate.Graphs.BCount108
import Candidate.Graphs.BCount109
import Candidate.Graphs.BCount110
import Candidate.Graphs.BCount111
import Candidate.Graphs.BCount112
import Candidate.Graphs.BCount113
import Candidate.Graphs.BCount114
import Candidate.Graphs.BCount115
import Candidate.Graphs.BCount116
import Candidate.Graphs.BCount117
import Candidate.Graphs.BCount118
import Candidate.Graphs.BCount119
import Candidate.Graphs.BCount120
import Candidate.Graphs.BCount121
import Candidate.Graphs.BCount122
import Candidate.Graphs.BCount123
import Candidate.Graphs.BCount124
import Candidate.Graphs.BCount125
import Candidate.Graphs.BCount126
import Candidate.Graphs.BCount127
import Candidate.Graphs.BCount128
import Candidate.Graphs.BCount129
import Candidate.Graphs.BCount130
import Candidate.Graphs.BCount131
import Candidate.Graphs.BCount132
import Candidate.Graphs.BCount133
import Candidate.Graphs.BCount134
import Candidate.Graphs.BCount135
import Candidate.Graphs.BCount136
import Candidate.Graphs.BCount137
import Candidate.Graphs.BCount138
import Candidate.Graphs.BCount139
import Candidate.Graphs.BCount140
import Candidate.Graphs.BCount141
import Candidate.Graphs.BCount142
import Candidate.Graphs.BCount143
import Candidate.Graphs.BCount144
import Candidate.Graphs.BCount145
import Candidate.Graphs.BCount146
import Candidate.Graphs.BCount147
import Candidate.Graphs.BCount148
import Candidate.Graphs.BCount149
import Candidate.Graphs.BCount150
import Candidate.Graphs.BCount151
import Candidate.Graphs.BCount152
import Candidate.Graphs.BCount153
import Candidate.Graphs.BCount154
import Candidate.Graphs.BCount155
import Candidate.Graphs.BCount156
import Candidate.Graphs.BCount157
import Candidate.Graphs.BCount158
import Candidate.Graphs.BCount159
import Candidate.Graphs.BCount160
import Candidate.Graphs.BCount161
import Candidate.Graphs.BCount162
import Candidate.Graphs.BCount163
import Candidate.Graphs.BCount164
import Candidate.Graphs.BCount165
import Candidate.Graphs.BCount166
import Candidate.Graphs.BCount167
import Candidate.Graphs.BCount168
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Das.QRH.GraphAssembly.BCount
open Record1252270103Finite
abbrev root : Source := Das.QRH.CoreBridge.toOriginal (Das.QRH.Graphs.BCount000.source000)
abbrev terminal : Source := Das.QRH.CoreBridge.toOriginal (Das.QRH.Graphs.BCount168.source023)
theorem advance (P : Source → Prop)
 (step : ∀(n low:Source), (n.allowance=1/10^17 ∧ n.lowFee=1/10^12 ∧ n.highFee=1/10^10) →
 SourceValid n low (some low) → P low → P n)
 (hroot : P root) : P terminal := by
 have h000 := Das.QRH.Graphs.BCount000.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) hroot
 have h001 := Das.QRH.Graphs.BCount001.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h000
 have h002 := Das.QRH.Graphs.BCount002.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h001
 have h003 := Das.QRH.Graphs.BCount003.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h002
 have h004 := Das.QRH.Graphs.BCount004.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h003
 have h005 := Das.QRH.Graphs.BCount005.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h004
 have h006 := Das.QRH.Graphs.BCount006.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h005
 have h007 := Das.QRH.Graphs.BCount007.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h006
 have h008 := Das.QRH.Graphs.BCount008.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h007
 have h009 := Das.QRH.Graphs.BCount009.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h008
 have h010 := Das.QRH.Graphs.BCount010.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h009
 have h011 := Das.QRH.Graphs.BCount011.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h010
 have h012 := Das.QRH.Graphs.BCount012.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h011
 have h013 := Das.QRH.Graphs.BCount013.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h012
 have h014 := Das.QRH.Graphs.BCount014.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h013
 have h015 := Das.QRH.Graphs.BCount015.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h014
 have h016 := Das.QRH.Graphs.BCount016.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h015
 have h017 := Das.QRH.Graphs.BCount017.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h016
 have h018 := Das.QRH.Graphs.BCount018.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h017
 have h019 := Das.QRH.Graphs.BCount019.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h018
 have h020 := Das.QRH.Graphs.BCount020.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h019
 have h021 := Das.QRH.Graphs.BCount021.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h020
 have h022 := Das.QRH.Graphs.BCount022.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h021
 have h023 := Das.QRH.Graphs.BCount023.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h022
 have h024 := Das.QRH.Graphs.BCount024.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h023
 have h025 := Das.QRH.Graphs.BCount025.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h024
 have h026 := Das.QRH.Graphs.BCount026.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h025
 have h027 := Das.QRH.Graphs.BCount027.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h026
 have h028 := Das.QRH.Graphs.BCount028.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h027
 have h029 := Das.QRH.Graphs.BCount029.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h028
 have h030 := Das.QRH.Graphs.BCount030.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h029
 have h031 := Das.QRH.Graphs.BCount031.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h030
 have h032 := Das.QRH.Graphs.BCount032.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h031
 have h033 := Das.QRH.Graphs.BCount033.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h032
 have h034 := Das.QRH.Graphs.BCount034.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h033
 have h035 := Das.QRH.Graphs.BCount035.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h034
 have h036 := Das.QRH.Graphs.BCount036.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h035
 have h037 := Das.QRH.Graphs.BCount037.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h036
 have h038 := Das.QRH.Graphs.BCount038.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h037
 have h039 := Das.QRH.Graphs.BCount039.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h038
 have h040 := Das.QRH.Graphs.BCount040.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h039
 have h041 := Das.QRH.Graphs.BCount041.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h040
 have h042 := Das.QRH.Graphs.BCount042.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h041
 have h043 := Das.QRH.Graphs.BCount043.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h042
 have h044 := Das.QRH.Graphs.BCount044.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h043
 have h045 := Das.QRH.Graphs.BCount045.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h044
 have h046 := Das.QRH.Graphs.BCount046.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h045
 have h047 := Das.QRH.Graphs.BCount047.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h046
 have h048 := Das.QRH.Graphs.BCount048.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h047
 have h049 := Das.QRH.Graphs.BCount049.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h048
 have h050 := Das.QRH.Graphs.BCount050.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h049
 have h051 := Das.QRH.Graphs.BCount051.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h050
 have h052 := Das.QRH.Graphs.BCount052.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h051
 have h053 := Das.QRH.Graphs.BCount053.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h052
 have h054 := Das.QRH.Graphs.BCount054.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h053
 have h055 := Das.QRH.Graphs.BCount055.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h054
 have h056 := Das.QRH.Graphs.BCount056.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h055
 have h057 := Das.QRH.Graphs.BCount057.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h056
 have h058 := Das.QRH.Graphs.BCount058.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h057
 have h059 := Das.QRH.Graphs.BCount059.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h058
 have h060 := Das.QRH.Graphs.BCount060.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h059
 have h061 := Das.QRH.Graphs.BCount061.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h060
 have h062 := Das.QRH.Graphs.BCount062.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h061
 have h063 := Das.QRH.Graphs.BCount063.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h062
 have h064 := Das.QRH.Graphs.BCount064.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h063
 have h065 := Das.QRH.Graphs.BCount065.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h064
 have h066 := Das.QRH.Graphs.BCount066.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h065
 have h067 := Das.QRH.Graphs.BCount067.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h066
 have h068 := Das.QRH.Graphs.BCount068.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h067
 have h069 := Das.QRH.Graphs.BCount069.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h068
 have h070 := Das.QRH.Graphs.BCount070.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h069
 have h071 := Das.QRH.Graphs.BCount071.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h070
 have h072 := Das.QRH.Graphs.BCount072.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h071
 have h073 := Das.QRH.Graphs.BCount073.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h072
 have h074 := Das.QRH.Graphs.BCount074.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h073
 have h075 := Das.QRH.Graphs.BCount075.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h074
 have h076 := Das.QRH.Graphs.BCount076.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h075
 have h077 := Das.QRH.Graphs.BCount077.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h076
 have h078 := Das.QRH.Graphs.BCount078.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h077
 have h079 := Das.QRH.Graphs.BCount079.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h078
 have h080 := Das.QRH.Graphs.BCount080.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h079
 have h081 := Das.QRH.Graphs.BCount081.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h080
 have h082 := Das.QRH.Graphs.BCount082.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h081
 have h083 := Das.QRH.Graphs.BCount083.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h082
 have h084 := Das.QRH.Graphs.BCount084.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h083
 have h085 := Das.QRH.Graphs.BCount085.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h084
 have h086 := Das.QRH.Graphs.BCount086.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h085
 have h087 := Das.QRH.Graphs.BCount087.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h086
 have h088 := Das.QRH.Graphs.BCount088.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h087
 have h089 := Das.QRH.Graphs.BCount089.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h088
 have h090 := Das.QRH.Graphs.BCount090.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h089
 have h091 := Das.QRH.Graphs.BCount091.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h090
 have h092 := Das.QRH.Graphs.BCount092.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h091
 have h093 := Das.QRH.Graphs.BCount093.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h092
 have h094 := Das.QRH.Graphs.BCount094.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h093
 have h095 := Das.QRH.Graphs.BCount095.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h094
 have h096 := Das.QRH.Graphs.BCount096.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h095
 have h097 := Das.QRH.Graphs.BCount097.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h096
 have h098 := Das.QRH.Graphs.BCount098.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h097
 have h099 := Das.QRH.Graphs.BCount099.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h098
 have h100 := Das.QRH.Graphs.BCount100.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h099
 have h101 := Das.QRH.Graphs.BCount101.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h100
 have h102 := Das.QRH.Graphs.BCount102.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h101
 have h103 := Das.QRH.Graphs.BCount103.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h102
 have h104 := Das.QRH.Graphs.BCount104.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h103
 have h105 := Das.QRH.Graphs.BCount105.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h104
 have h106 := Das.QRH.Graphs.BCount106.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h105
 have h107 := Das.QRH.Graphs.BCount107.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h106
 have h108 := Das.QRH.Graphs.BCount108.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h107
 have h109 := Das.QRH.Graphs.BCount109.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h108
 have h110 := Das.QRH.Graphs.BCount110.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h109
 have h111 := Das.QRH.Graphs.BCount111.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h110
 have h112 := Das.QRH.Graphs.BCount112.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h111
 have h113 := Das.QRH.Graphs.BCount113.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h112
 have h114 := Das.QRH.Graphs.BCount114.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h113
 have h115 := Das.QRH.Graphs.BCount115.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h114
 have h116 := Das.QRH.Graphs.BCount116.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h115
 have h117 := Das.QRH.Graphs.BCount117.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h116
 have h118 := Das.QRH.Graphs.BCount118.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h117
 have h119 := Das.QRH.Graphs.BCount119.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h118
 have h120 := Das.QRH.Graphs.BCount120.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h119
 have h121 := Das.QRH.Graphs.BCount121.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h120
 have h122 := Das.QRH.Graphs.BCount122.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h121
 have h123 := Das.QRH.Graphs.BCount123.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h122
 have h124 := Das.QRH.Graphs.BCount124.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h123
 have h125 := Das.QRH.Graphs.BCount125.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h124
 have h126 := Das.QRH.Graphs.BCount126.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h125
 have h127 := Das.QRH.Graphs.BCount127.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h126
 have h128 := Das.QRH.Graphs.BCount128.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h127
 have h129 := Das.QRH.Graphs.BCount129.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h128
 have h130 := Das.QRH.Graphs.BCount130.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h129
 have h131 := Das.QRH.Graphs.BCount131.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h130
 have h132 := Das.QRH.Graphs.BCount132.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h131
 have h133 := Das.QRH.Graphs.BCount133.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h132
 have h134 := Das.QRH.Graphs.BCount134.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h133
 have h135 := Das.QRH.Graphs.BCount135.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h134
 have h136 := Das.QRH.Graphs.BCount136.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h135
 have h137 := Das.QRH.Graphs.BCount137.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h136
 have h138 := Das.QRH.Graphs.BCount138.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h137
 have h139 := Das.QRH.Graphs.BCount139.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h138
 have h140 := Das.QRH.Graphs.BCount140.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h139
 have h141 := Das.QRH.Graphs.BCount141.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h140
 have h142 := Das.QRH.Graphs.BCount142.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h141
 have h143 := Das.QRH.Graphs.BCount143.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h142
 have h144 := Das.QRH.Graphs.BCount144.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h143
 have h145 := Das.QRH.Graphs.BCount145.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h144
 have h146 := Das.QRH.Graphs.BCount146.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h145
 have h147 := Das.QRH.Graphs.BCount147.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h146
 have h148 := Das.QRH.Graphs.BCount148.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h147
 have h149 := Das.QRH.Graphs.BCount149.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h148
 have h150 := Das.QRH.Graphs.BCount150.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h149
 have h151 := Das.QRH.Graphs.BCount151.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h150
 have h152 := Das.QRH.Graphs.BCount152.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h151
 have h153 := Das.QRH.Graphs.BCount153.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h152
 have h154 := Das.QRH.Graphs.BCount154.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h153
 have h155 := Das.QRH.Graphs.BCount155.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h154
 have h156 := Das.QRH.Graphs.BCount156.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h155
 have h157 := Das.QRH.Graphs.BCount157.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h156
 have h158 := Das.QRH.Graphs.BCount158.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h157
 have h159 := Das.QRH.Graphs.BCount159.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h158
 have h160 := Das.QRH.Graphs.BCount160.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h159
 have h161 := Das.QRH.Graphs.BCount161.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h160
 have h162 := Das.QRH.Graphs.BCount162.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h161
 have h163 := Das.QRH.Graphs.BCount163.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h162
 have h164 := Das.QRH.Graphs.BCount164.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h163
 have h165 := Das.QRH.Graphs.BCount165.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h164
 have h166 := Das.QRH.Graphs.BCount166.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h165
 have h167 := Das.QRH.Graphs.BCount167.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h166
 have h168 := Das.QRH.Graphs.BCount168.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h167
 exact h168
end Das.QRH.GraphAssembly.BCount
#print axioms Das.QRH.GraphAssembly.BCount.advance
