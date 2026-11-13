/- Subhanjan Das; MIT for new assembly; AI-assisted with OpenAI Codex. -/
import Candidate.CoreBridge
import Candidate.Graphs.ACount000
import Candidate.Graphs.ACount001
import Candidate.Graphs.ACount002
import Candidate.Graphs.ACount003
import Candidate.Graphs.ACount004
import Candidate.Graphs.ACount005
import Candidate.Graphs.ACount006
import Candidate.Graphs.ACount007
import Candidate.Graphs.ACount008
import Candidate.Graphs.ACount009
import Candidate.Graphs.ACount010
import Candidate.Graphs.ACount011
import Candidate.Graphs.ACount012
import Candidate.Graphs.ACount013
import Candidate.Graphs.ACount014
import Candidate.Graphs.ACount015
import Candidate.Graphs.ACount016
import Candidate.Graphs.ACount017
import Candidate.Graphs.ACount018
import Candidate.Graphs.ACount019
import Candidate.Graphs.ACount020
import Candidate.Graphs.ACount021
import Candidate.Graphs.ACount022
import Candidate.Graphs.ACount023
import Candidate.Graphs.ACount024
import Candidate.Graphs.ACount025
import Candidate.Graphs.ACount026
import Candidate.Graphs.ACount027
import Candidate.Graphs.ACount028
import Candidate.Graphs.ACount029
import Candidate.Graphs.ACount030
import Candidate.Graphs.ACount031
import Candidate.Graphs.ACount032
import Candidate.Graphs.ACount033
import Candidate.Graphs.ACount034
import Candidate.Graphs.ACount035
import Candidate.Graphs.ACount036
import Candidate.Graphs.ACount037
import Candidate.Graphs.ACount038
import Candidate.Graphs.ACount039
import Candidate.Graphs.ACount040
import Candidate.Graphs.ACount041
import Candidate.Graphs.ACount042
import Candidate.Graphs.ACount043
import Candidate.Graphs.ACount044
import Candidate.Graphs.ACount045
import Candidate.Graphs.ACount046
import Candidate.Graphs.ACount047
import Candidate.Graphs.ACount048
import Candidate.Graphs.ACount049
import Candidate.Graphs.ACount050
import Candidate.Graphs.ACount051
import Candidate.Graphs.ACount052
import Candidate.Graphs.ACount053
import Candidate.Graphs.ACount054
import Candidate.Graphs.ACount055
import Candidate.Graphs.ACount056
import Candidate.Graphs.ACount057
import Candidate.Graphs.ACount058
import Candidate.Graphs.ACount059
import Candidate.Graphs.ACount060
import Candidate.Graphs.ACount061
import Candidate.Graphs.ACount062
import Candidate.Graphs.ACount063
import Candidate.Graphs.ACount064
import Candidate.Graphs.ACount065
import Candidate.Graphs.ACount066
import Candidate.Graphs.ACount067
import Candidate.Graphs.ACount068
import Candidate.Graphs.ACount069
import Candidate.Graphs.ACount070
import Candidate.Graphs.ACount071
import Candidate.Graphs.ACount072
import Candidate.Graphs.ACount073
import Candidate.Graphs.ACount074
import Candidate.Graphs.ACount075
import Candidate.Graphs.ACount076
import Candidate.Graphs.ACount077
import Candidate.Graphs.ACount078
import Candidate.Graphs.ACount079
import Candidate.Graphs.ACount080
import Candidate.Graphs.ACount081
import Candidate.Graphs.ACount082
import Candidate.Graphs.ACount083
import Candidate.Graphs.ACount084
import Candidate.Graphs.ACount085
import Candidate.Graphs.ACount086
import Candidate.Graphs.ACount087
import Candidate.Graphs.ACount088
import Candidate.Graphs.ACount089
import Candidate.Graphs.ACount090
import Candidate.Graphs.ACount091
import Candidate.Graphs.ACount092
import Candidate.Graphs.ACount093
import Candidate.Graphs.ACount094
import Candidate.Graphs.ACount095
import Candidate.Graphs.ACount096
import Candidate.Graphs.ACount097
import Candidate.Graphs.ACount098
import Candidate.Graphs.ACount099
import Candidate.Graphs.ACount100
import Candidate.Graphs.ACount101
import Candidate.Graphs.ACount102
import Candidate.Graphs.ACount103
import Candidate.Graphs.ACount104
import Candidate.Graphs.ACount105
import Candidate.Graphs.ACount106
import Candidate.Graphs.ACount107
import Candidate.Graphs.ACount108
import Candidate.Graphs.ACount109
import Candidate.Graphs.ACount110
import Candidate.Graphs.ACount111
import Candidate.Graphs.ACount112
import Candidate.Graphs.ACount113
import Candidate.Graphs.ACount114
import Candidate.Graphs.ACount115
import Candidate.Graphs.ACount116
import Candidate.Graphs.ACount117
import Candidate.Graphs.ACount118
import Candidate.Graphs.ACount119
import Candidate.Graphs.ACount120
import Candidate.Graphs.ACount121
import Candidate.Graphs.ACount122
import Candidate.Graphs.ACount123
import Candidate.Graphs.ACount124
import Candidate.Graphs.ACount125
import Candidate.Graphs.ACount126
import Candidate.Graphs.ACount127
import Candidate.Graphs.ACount128
import Candidate.Graphs.ACount129
import Candidate.Graphs.ACount130
import Candidate.Graphs.ACount131
import Candidate.Graphs.ACount132
import Candidate.Graphs.ACount133
import Candidate.Graphs.ACount134
import Candidate.Graphs.ACount135
import Candidate.Graphs.ACount136
import Candidate.Graphs.ACount137
import Candidate.Graphs.ACount138
import Candidate.Graphs.ACount139
import Candidate.Graphs.ACount140
import Candidate.Graphs.ACount141
import Candidate.Graphs.ACount142
import Candidate.Graphs.ACount143
import Candidate.Graphs.ACount144
import Candidate.Graphs.ACount145
import Candidate.Graphs.ACount146
import Candidate.Graphs.ACount147
import Candidate.Graphs.ACount148
import Candidate.Graphs.ACount149
import Candidate.Graphs.ACount150
import Candidate.Graphs.ACount151
import Candidate.Graphs.ACount152
import Candidate.Graphs.ACount153
import Candidate.Graphs.ACount154
import Candidate.Graphs.ACount155
import Candidate.Graphs.ACount156
import Candidate.Graphs.ACount157
import Candidate.Graphs.ACount158
import Candidate.Graphs.ACount159
import Candidate.Graphs.ACount160
import Candidate.Graphs.ACount161
import Candidate.Graphs.ACount162
import Candidate.Graphs.ACount163
import Candidate.Graphs.ACount164
import Candidate.Graphs.ACount165
import Candidate.Graphs.ACount166
import Candidate.Graphs.ACount167
import Candidate.Graphs.ACount168
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Das.QRH.GraphAssembly.ACount
open Record1252270103Finite
abbrev root : Source := Das.QRH.Graphs.ACount000.source000
abbrev terminal : Source := Das.QRH.CoreBridge.toOriginal (Das.QRH.Graphs.ACount168.source023)
theorem advance (P : Source → Prop)
 (step : ∀(n low:Source), (n.allowance=1/10^17 ∧ n.lowFee=1/10^12 ∧ n.highFee=1/10^10) →
 SourceValid n low (some low) → P low → P n)
 (hroot : P root) : P terminal := by
 have h000 := Das.QRH.Graphs.ACount000.advance P step hroot
 have h001 := Das.QRH.Graphs.ACount001.advance P step h000
 have h002 := Das.QRH.Graphs.ACount002.advance P step h001
 have h003 := Das.QRH.Graphs.ACount003.advance P step h002
 have h004 := Das.QRH.Graphs.ACount004.advance P step h003
 have h005 := Das.QRH.Graphs.ACount005.advance P step h004
 have h006 := Das.QRH.Graphs.ACount006.advance P step h005
 have h007 := Das.QRH.Graphs.ACount007.advance P step h006
 have h008 := Das.QRH.Graphs.ACount008.advance P step h007
 have h009 := Das.QRH.Graphs.ACount009.advance P step h008
 have h010 := Das.QRH.Graphs.ACount010.advance P step h009
 have h011 := Das.QRH.Graphs.ACount011.advance P step h010
 have h012 := Das.QRH.Graphs.ACount012.advance P step h011
 have h013 := Das.QRH.Graphs.ACount013.advance P step h012
 have h014 := Das.QRH.Graphs.ACount014.advance P step h013
 have h015 := Das.QRH.Graphs.ACount015.advance P step h014
 have h016 := Das.QRH.Graphs.ACount016.advance P step h015
 have h017 := Das.QRH.Graphs.ACount017.advance P step h016
 have h018 := Das.QRH.Graphs.ACount018.advance P step h017
 have h019 := Das.QRH.Graphs.ACount019.advance P step h018
 have h020 := Das.QRH.Graphs.ACount020.advance P step h019
 have h021 := Das.QRH.Graphs.ACount021.advance P step h020
 have h022 := Das.QRH.Graphs.ACount022.advance P step h021
 have h023 := Das.QRH.Graphs.ACount023.advance P step h022
 have h024 := Das.QRH.Graphs.ACount024.advance P step h023
 have h025 := Das.QRH.Graphs.ACount025.advance P step h024
 have h026 := Das.QRH.Graphs.ACount026.advance P step h025
 have h027 := Das.QRH.Graphs.ACount027.advance P step h026
 have h028 := Das.QRH.Graphs.ACount028.advance P step h027
 have h029 := Das.QRH.Graphs.ACount029.advance P step h028
 have h030 := Das.QRH.Graphs.ACount030.advance P step h029
 have h031 := Das.QRH.Graphs.ACount031.advance P step h030
 have h032 := Das.QRH.Graphs.ACount032.advance P step h031
 have h033 := Das.QRH.Graphs.ACount033.advance P step h032
 have h034 := Das.QRH.Graphs.ACount034.advance P step h033
 have h035 := Das.QRH.Graphs.ACount035.advance P step h034
 have h036 := Das.QRH.Graphs.ACount036.advance P step h035
 have h037 := Das.QRH.Graphs.ACount037.advance P step h036
 have h038 := Das.QRH.Graphs.ACount038.advance P step h037
 have h039 := Das.QRH.Graphs.ACount039.advance P step h038
 have h040 := Das.QRH.Graphs.ACount040.advance P step h039
 have h041 := Das.QRH.Graphs.ACount041.advance P step h040
 have h042 := Das.QRH.Graphs.ACount042.advance P step h041
 have h043 := Das.QRH.Graphs.ACount043.advance P step h042
 have h044 := Das.QRH.Graphs.ACount044.advance P step h043
 have h045 := Das.QRH.Graphs.ACount045.advance P step h044
 have h046 := Das.QRH.Graphs.ACount046.advance P step h045
 have h047 := Das.QRH.Graphs.ACount047.advance P step h046
 have h048 := Das.QRH.Graphs.ACount048.advance P step h047
 have h049 := Das.QRH.Graphs.ACount049.advance P step h048
 have h050 := Das.QRH.Graphs.ACount050.advance P step h049
 have h051 := Das.QRH.Graphs.ACount051.advance P step h050
 have h052 := Das.QRH.Graphs.ACount052.advance P step h051
 have h053 := Das.QRH.Graphs.ACount053.advance P step h052
 have h054 := Das.QRH.Graphs.ACount054.advance P step h053
 have h055 := Das.QRH.Graphs.ACount055.advance P step h054
 have h056 := Das.QRH.Graphs.ACount056.advance P step h055
 have h057 := Das.QRH.Graphs.ACount057.advance P step h056
 have h058 := Das.QRH.Graphs.ACount058.advance P step h057
 have h059 := Das.QRH.Graphs.ACount059.advance P step h058
 have h060 := Das.QRH.Graphs.ACount060.advance P step h059
 have h061 := Das.QRH.Graphs.ACount061.advance P step h060
 have h062 := Das.QRH.Graphs.ACount062.advance P step h061
 have h063 := Das.QRH.Graphs.ACount063.advance P step h062
 have h064 := Das.QRH.Graphs.ACount064.advance P step h063
 have h065 := Das.QRH.Graphs.ACount065.advance P step h064
 have h066 := Das.QRH.Graphs.ACount066.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h065
 have h067 := Das.QRH.Graphs.ACount067.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h066
 have h068 := Das.QRH.Graphs.ACount068.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h067
 have h069 := Das.QRH.Graphs.ACount069.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h068
 have h070 := Das.QRH.Graphs.ACount070.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h069
 have h071 := Das.QRH.Graphs.ACount071.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h070
 have h072 := Das.QRH.Graphs.ACount072.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h071
 have h073 := Das.QRH.Graphs.ACount073.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h072
 have h074 := Das.QRH.Graphs.ACount074.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h073
 have h075 := Das.QRH.Graphs.ACount075.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h074
 have h076 := Das.QRH.Graphs.ACount076.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h075
 have h077 := Das.QRH.Graphs.ACount077.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h076
 have h078 := Das.QRH.Graphs.ACount078.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h077
 have h079 := Das.QRH.Graphs.ACount079.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h078
 have h080 := Das.QRH.Graphs.ACount080.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h079
 have h081 := Das.QRH.Graphs.ACount081.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h080
 have h082 := Das.QRH.Graphs.ACount082.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h081
 have h083 := Das.QRH.Graphs.ACount083.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h082
 have h084 := Das.QRH.Graphs.ACount084.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h083
 have h085 := Das.QRH.Graphs.ACount085.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h084
 have h086 := Das.QRH.Graphs.ACount086.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h085
 have h087 := Das.QRH.Graphs.ACount087.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h086
 have h088 := Das.QRH.Graphs.ACount088.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h087
 have h089 := Das.QRH.Graphs.ACount089.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h088
 have h090 := Das.QRH.Graphs.ACount090.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h089
 have h091 := Das.QRH.Graphs.ACount091.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h090
 have h092 := Das.QRH.Graphs.ACount092.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h091
 have h093 := Das.QRH.Graphs.ACount093.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h092
 have h094 := Das.QRH.Graphs.ACount094.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h093
 have h095 := Das.QRH.Graphs.ACount095.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h094
 have h096 := Das.QRH.Graphs.ACount096.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h095
 have h097 := Das.QRH.Graphs.ACount097.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h096
 have h098 := Das.QRH.Graphs.ACount098.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h097
 have h099 := Das.QRH.Graphs.ACount099.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h098
 have h100 := Das.QRH.Graphs.ACount100.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h099
 have h101 := Das.QRH.Graphs.ACount101.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h100
 have h102 := Das.QRH.Graphs.ACount102.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h101
 have h103 := Das.QRH.Graphs.ACount103.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h102
 have h104 := Das.QRH.Graphs.ACount104.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h103
 have h105 := Das.QRH.Graphs.ACount105.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h104
 have h106 := Das.QRH.Graphs.ACount106.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h105
 have h107 := Das.QRH.Graphs.ACount107.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h106
 have h108 := Das.QRH.Graphs.ACount108.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h107
 have h109 := Das.QRH.Graphs.ACount109.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h108
 have h110 := Das.QRH.Graphs.ACount110.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h109
 have h111 := Das.QRH.Graphs.ACount111.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h110
 have h112 := Das.QRH.Graphs.ACount112.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h111
 have h113 := Das.QRH.Graphs.ACount113.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h112
 have h114 := Das.QRH.Graphs.ACount114.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h113
 have h115 := Das.QRH.Graphs.ACount115.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h114
 have h116 := Das.QRH.Graphs.ACount116.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h115
 have h117 := Das.QRH.Graphs.ACount117.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h116
 have h118 := Das.QRH.Graphs.ACount118.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h117
 have h119 := Das.QRH.Graphs.ACount119.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h118
 have h120 := Das.QRH.Graphs.ACount120.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h119
 have h121 := Das.QRH.Graphs.ACount121.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h120
 have h122 := Das.QRH.Graphs.ACount122.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h121
 have h123 := Das.QRH.Graphs.ACount123.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h122
 have h124 := Das.QRH.Graphs.ACount124.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h123
 have h125 := Das.QRH.Graphs.ACount125.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h124
 have h126 := Das.QRH.Graphs.ACount126.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h125
 have h127 := Das.QRH.Graphs.ACount127.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h126
 have h128 := Das.QRH.Graphs.ACount128.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h127
 have h129 := Das.QRH.Graphs.ACount129.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h128
 have h130 := Das.QRH.Graphs.ACount130.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h129
 have h131 := Das.QRH.Graphs.ACount131.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h130
 have h132 := Das.QRH.Graphs.ACount132.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h131
 have h133 := Das.QRH.Graphs.ACount133.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h132
 have h134 := Das.QRH.Graphs.ACount134.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h133
 have h135 := Das.QRH.Graphs.ACount135.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h134
 have h136 := Das.QRH.Graphs.ACount136.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h135
 have h137 := Das.QRH.Graphs.ACount137.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h136
 have h138 := Das.QRH.Graphs.ACount138.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h137
 have h139 := Das.QRH.Graphs.ACount139.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h138
 have h140 := Das.QRH.Graphs.ACount140.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h139
 have h141 := Das.QRH.Graphs.ACount141.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h140
 have h142 := Das.QRH.Graphs.ACount142.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h141
 have h143 := Das.QRH.Graphs.ACount143.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h142
 have h144 := Das.QRH.Graphs.ACount144.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h143
 have h145 := Das.QRH.Graphs.ACount145.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h144
 have h146 := Das.QRH.Graphs.ACount146.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h145
 have h147 := Das.QRH.Graphs.ACount147.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h146
 have h148 := Das.QRH.Graphs.ACount148.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h147
 have h149 := Das.QRH.Graphs.ACount149.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h148
 have h150 := Das.QRH.Graphs.ACount150.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h149
 have h151 := Das.QRH.Graphs.ACount151.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h150
 have h152 := Das.QRH.Graphs.ACount152.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h151
 have h153 := Das.QRH.Graphs.ACount153.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h152
 have h154 := Das.QRH.Graphs.ACount154.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h153
 have h155 := Das.QRH.Graphs.ACount155.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h154
 have h156 := Das.QRH.Graphs.ACount156.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h155
 have h157 := Das.QRH.Graphs.ACount157.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h156
 have h158 := Das.QRH.Graphs.ACount158.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h157
 have h159 := Das.QRH.Graphs.ACount159.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h158
 have h160 := Das.QRH.Graphs.ACount160.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h159
 have h161 := Das.QRH.Graphs.ACount161.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h160
 have h162 := Das.QRH.Graphs.ACount162.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h161
 have h163 := Das.QRH.Graphs.ACount163.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h162
 have h164 := Das.QRH.Graphs.ACount164.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h163
 have h165 := Das.QRH.Graphs.ACount165.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h164
 have h166 := Das.QRH.Graphs.ACount166.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h165
 have h167 := Das.QRH.Graphs.ACount167.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h166
 have h168 := Das.QRH.Graphs.ACount168.advance (fun n => P (Das.QRH.CoreBridge.toOriginal n)) (fun n low ha hv hl => step (Das.QRH.CoreBridge.toOriginal n) (Das.QRH.CoreBridge.toOriginal low) ha (Das.QRH.CoreBridge.sound n low hv) hl) h167
 exact h168
end Das.QRH.GraphAssembly.ACount
#print axioms Das.QRH.GraphAssembly.ACount.advance
