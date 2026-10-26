/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.IntermediateCount.EnvelopeBounds
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return001
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return002
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return003
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return004
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return005
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return006
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return007
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return008
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return009
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return010
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return011
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return012
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return013
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return014
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return015
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return016
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return017
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return018
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return019
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return020
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return021
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return022
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return023
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return024
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return025
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return026
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return027
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return028
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return029
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return030
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return031
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return032
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return033
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return034
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return035
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return036
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return037
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return038
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return039
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return040
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return041
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return042
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return043
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return044
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return045
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return046
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return047
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return048
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return049
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return050
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return051
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return052
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return053
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return054
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return055
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return056
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return057
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return058
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return059
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return060
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return061
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return062
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return063
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return064
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return065
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return066
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return067
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return068
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return069
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return070
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return071
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return072
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return073
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return074
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return075
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return076
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return077
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return078
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return079
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return080
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return081
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return082
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return083
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return084
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return085
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return086
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return087
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return088
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return089
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return090
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return091
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return092
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return093
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return094
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return095
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return096
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return097
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return098
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return099
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return100
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return101
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return102
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return103
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return104
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return105
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return106
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return107
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return108
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return109
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return110
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return111
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return112
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return113
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return114
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return115
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return116
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return117
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return118
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return119
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return120
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return121
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return122
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return123
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return124
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return125
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return126
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return127
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return128
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return129
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return130
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return131
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return132
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return133
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return134
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return135
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return136
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return137
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return138
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return139
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return140
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return141
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return142
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return143
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return144
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return145
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return146
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return147
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return148
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return149
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return150
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return151
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return152
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return153
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return154
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return155
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return156
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return157
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return158
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return159
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return160
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return161
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return162
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return163
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return164
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return165
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return166
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return167
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return168
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return169
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return170
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return171
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return172
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return173
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return174
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return175
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return176
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return177
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return178
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return179
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return180
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return181
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return182
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return183
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return184
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return185
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return186
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return187
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return188
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return189
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return190
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return191
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return192
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return193
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return194
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return195
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return196
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return197
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return198
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return199
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return200
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return201
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return202
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return203
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return204
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return205
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return206
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return207
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return208
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return209
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return210
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return211
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.Return212
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.LewkoStage1Return.IntermediateCount.Edges
noncomputable section
open LewkoStage1Return.C30
theorem window04_mem : returnWindow04∈returnWindows := by simp [returnWindows]
theorem window06_mem : returnWindow06∈returnWindows := by simp [returnWindows]
theorem window07_mem : returnWindow07∈returnWindows := by simp [returnWindows]
theorem window08_mem : returnWindow08∈returnWindows := by simp [returnWindows]
theorem window09_mem : returnWindow09∈returnWindows := by simp [returnWindows]
theorem window10_mem : returnWindow10∈returnWindows := by simp [returnWindows]
theorem window11_mem : returnWindow11∈returnWindows := by simp [returnWindows]
theorem window12_mem : returnWindow12∈returnWindows := by simp [returnWindows]
theorem window13_mem : returnWindow13∈returnWindows := by simp [returnWindows]
theorem window14_mem : returnWindow14∈returnWindows := by simp [returnWindows]
theorem window15_mem : returnWindow15∈returnWindows := by simp [returnWindows]
theorem window16_mem : returnWindow16∈returnWindows := by simp [returnWindows]
theorem window17_mem : returnWindow17∈returnWindows := by simp [returnWindows]
theorem window18_mem : returnWindow18∈returnWindows := by simp [returnWindows]
theorem window19_mem : returnWindow19∈returnWindows := by simp [returnWindows]
theorem window20_mem : returnWindow20∈returnWindows := by simp [returnWindows]
theorem window21_mem : returnWindow21∈returnWindows := by simp [returnWindows]
theorem window22_mem : returnWindow22∈returnWindows := by simp [returnWindows]
theorem window23_mem : returnWindow23∈returnWindows := by simp [returnWindows]
theorem window24_mem : returnWindow24∈returnWindows := by simp [returnWindows]
theorem window27_mem : returnWindow27∈returnWindows := by simp [returnWindows]
theorem window28_mem : returnWindow28∈returnWindows := by simp [returnWindows]
theorem window29_mem : returnWindow29∈returnWindows := by simp [returnWindows]
theorem window30_mem : returnWindow30∈returnWindows := by simp [returnWindows]
theorem window31_mem : returnWindow31∈returnWindows := by simp [returnWindows]
theorem window35_mem : returnWindow35∈returnWindows := by simp [returnWindows]
theorem window36_mem : returnWindow36∈returnWindows := by simp [returnWindows]
theorem envelope_row001 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row001_pos hδ hp) hR
theorem envelope_row002 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row002_pos hδ hp) hR
theorem envelope_row003 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row003_pos hδ hp) hR
theorem envelope_row004 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row004_pos hδ hp) hR
theorem envelope_row005 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow04.Available δ p := by
  change δ∈Set.Icc (3/8:ℝ) (27/64:ℝ) ∧ p∈Set.Icc (7/16:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow04 window04_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row005_pos hδ hp) hR
theorem envelope_row006 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row006_pos hδ hp) hR
theorem envelope_row007 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow06.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capP δ p/countJ .capP δ p := finiteEnvelope_le_window returnWindow06 window06_mem ha
 exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row007_pos hδ hp) hR
theorem envelope_row008 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow07.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (111/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow07 window07_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row008_pos hδ hp) hR
theorem envelope_row009 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow08.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC8 δ p/countJ .weakC8 δ p := finiteEnvelope_le_window returnWindow08 window08_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC8 hd0 hp0) (row009_pos hδ hp) hR
theorem envelope_row010 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow09.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC6 δ p/countJ .weakC6 δ p := finiteEnvelope_le_window returnWindow09 window09_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC6 hd0 hp0) (row010_pos hδ hp) hR
theorem envelope_row011 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow10.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC2 δ p/countJ .weakC2 δ p := finiteEnvelope_le_window returnWindow10 window10_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC2 hd0 hp0) (row011_pos hδ hp) hR
theorem envelope_row012 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow11.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow11 window11_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row012_pos hδ hp) hR
theorem envelope_row013 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow12.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow12 window12_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row013_pos hδ hp) hR
theorem envelope_row014 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow13.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow13 window13_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row014_pos hδ hp) hR
theorem envelope_row015 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow14.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (255/512:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow14 window14_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row015_pos hδ hp) hR
theorem envelope_row016 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow15.Available δ p := by
  change δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow15 window15_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row016_pos hδ hp) hR
theorem envelope_row017 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow16.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow16 window16_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row017_pos hδ hp) hR
theorem envelope_row018 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow17.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow17 window17_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row018_pos hδ hp) hR
theorem envelope_row019 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow18.Available δ p := by
  change δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow18 window18_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row019_pos hδ hp) hR
theorem envelope_row020 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow19.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow19 window19_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row020_pos hδ hp) hR
theorem envelope_row021 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow20.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (237/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow20 window20_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row021_pos hδ hp) hR
theorem envelope_row022 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow21.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow21 window21_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row022_pos hδ hp) hR
theorem envelope_row023 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow22.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow22 window22_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row023_pos hδ hp) hR
theorem envelope_row024 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow23.Available δ p := by
  change δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow23 window23_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row024_pos hδ hp) hR
theorem envelope_row025 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow24.Available δ p := by
  change δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow24 window24_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row025_pos hδ hp) hR
theorem envelope_row026 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row026_pos hδ hp) hR
theorem envelope_row027 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row027_pos hδ hp) hR
theorem envelope_row028 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow27.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow27 window27_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row028_pos hδ hp) hR
theorem envelope_row029 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow28.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow28 window28_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row029_pos hδ hp) hR
theorem envelope_row030 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow29.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow29 window29_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row030_pos hδ hp) hR
theorem envelope_row031 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow30.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow30 window30_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row031_pos hδ hp) hR
theorem envelope_row032 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow31.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow31 window31_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row032_pos hδ hp) hR
theorem envelope_row033 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row033_pos hδ hp) hR
theorem envelope_row034 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row034_pos hδ hp) hR
theorem envelope_row035 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row035_pos hδ hp) hR
theorem envelope_row036 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row036_pos hδ hp) hR
theorem envelope_row037 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row037_pos hδ hp) hR
theorem envelope_row038 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row038_pos hδ hp) hR
theorem envelope_row039 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row039_pos hδ hp) hR
theorem envelope_row040 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow04.Available δ p := by
  change δ∈Set.Icc (3/8:ℝ) (27/64:ℝ) ∧ p∈Set.Icc (7/16:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow04 window04_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row040_pos hδ hp) hR
theorem envelope_row041 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row041_pos hδ hp) hR
theorem envelope_row042 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow06.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capP δ p/countJ .capP δ p := finiteEnvelope_le_window returnWindow06 window06_mem ha
 exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row042_pos hδ hp) hR
theorem envelope_row043 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow07.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (111/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow07 window07_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row043_pos hδ hp) hR
theorem envelope_row044 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow08.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC8 δ p/countJ .weakC8 δ p := finiteEnvelope_le_window returnWindow08 window08_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC8 hd0 hp0) (row044_pos hδ hp) hR
theorem envelope_row045 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow09.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC6 δ p/countJ .weakC6 δ p := finiteEnvelope_le_window returnWindow09 window09_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC6 hd0 hp0) (row045_pos hδ hp) hR
theorem envelope_row046 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow10.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC2 δ p/countJ .weakC2 δ p := finiteEnvelope_le_window returnWindow10 window10_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC2 hd0 hp0) (row046_pos hδ hp) hR
theorem envelope_row047 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow11.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow11 window11_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row047_pos hδ hp) hR
theorem envelope_row048 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow12.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow12 window12_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row048_pos hδ hp) hR
theorem envelope_row049 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow13.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow13 window13_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row049_pos hδ hp) hR
theorem envelope_row050 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow14.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (255/512:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow14 window14_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row050_pos hδ hp) hR
theorem envelope_row051 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow15.Available δ p := by
  change δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow15 window15_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row051_pos hδ hp) hR
theorem envelope_row052 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow16.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow16 window16_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row052_pos hδ hp) hR
theorem envelope_row053 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow17.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow17 window17_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row053_pos hδ hp) hR
theorem envelope_row054 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow18.Available δ p := by
  change δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow18 window18_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row054_pos hδ hp) hR
theorem envelope_row055 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow19.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow19 window19_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row055_pos hδ hp) hR
theorem envelope_row056 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow20.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (237/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow20 window20_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row056_pos hδ hp) hR
theorem envelope_row057 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow21.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow21 window21_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row057_pos hδ hp) hR
theorem envelope_row058 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow22.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow22 window22_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row058_pos hδ hp) hR
theorem envelope_row059 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow23.Available δ p := by
  change δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow23 window23_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row059_pos hδ hp) hR
theorem envelope_row060 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow24.Available δ p := by
  change δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow24 window24_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row060_pos hδ hp) hR
theorem envelope_row061 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row061_pos hδ hp) hR
theorem envelope_row062 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row062_pos hδ hp) hR
theorem envelope_row063 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow27.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow27 window27_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row063_pos hδ hp) hR
theorem envelope_row064 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow28.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow28 window28_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row064_pos hδ hp) hR
theorem envelope_row065 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow29.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow29 window29_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row065_pos hδ hp) hR
theorem envelope_row066 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow30.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow30 window30_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row066_pos hδ hp) hR
theorem envelope_row067 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow31.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow31 window31_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row067_pos hδ hp) hR
theorem envelope_row068 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row068_pos hδ hp) hR
theorem envelope_row069 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row069_pos hδ hp) hR
theorem envelope_row070 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row070_pos hδ hp) hR
theorem envelope_row071 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row071_pos hδ hp) hR
theorem envelope_row072 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row072_pos hδ hp) hR
theorem envelope_row073 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row073_pos hδ hp) hR
theorem envelope_row074 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row074_pos hδ hp) hR
theorem envelope_row075 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow04.Available δ p := by
  change δ∈Set.Icc (3/8:ℝ) (27/64:ℝ) ∧ p∈Set.Icc (7/16:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow04 window04_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row075_pos hδ hp) hR
theorem envelope_row076 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row076_pos hδ hp) hR
theorem envelope_row077 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow06.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capP δ p/countJ .capP δ p := finiteEnvelope_le_window returnWindow06 window06_mem ha
 exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row077_pos hδ hp) hR
theorem envelope_row078 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow07.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (111/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow07 window07_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row078_pos hδ hp) hR
theorem envelope_row079 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow08.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC8 δ p/countJ .weakC8 δ p := finiteEnvelope_le_window returnWindow08 window08_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC8 hd0 hp0) (row079_pos hδ hp) hR
theorem envelope_row080 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow09.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC6 δ p/countJ .weakC6 δ p := finiteEnvelope_le_window returnWindow09 window09_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC6 hd0 hp0) (row080_pos hδ hp) hR
theorem envelope_row081 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow10.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC2 δ p/countJ .weakC2 δ p := finiteEnvelope_le_window returnWindow10 window10_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC2 hd0 hp0) (row081_pos hδ hp) hR
theorem envelope_row082 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow11.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow11 window11_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row082_pos hδ hp) hR
theorem envelope_row083 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow12.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow12 window12_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row083_pos hδ hp) hR
theorem envelope_row084 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow13.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow13 window13_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row084_pos hδ hp) hR
theorem envelope_row085 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow14.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (255/512:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow14 window14_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row085_pos hδ hp) hR
theorem envelope_row086 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow15.Available δ p := by
  change δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow15 window15_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row086_pos hδ hp) hR
theorem envelope_row087 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow16.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow16 window16_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row087_pos hδ hp) hR
theorem envelope_row088 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow17.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow17 window17_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row088_pos hδ hp) hR
theorem envelope_row089 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow18.Available δ p := by
  change δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow18 window18_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row089_pos hδ hp) hR
theorem envelope_row090 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow19.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow19 window19_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row090_pos hδ hp) hR
theorem envelope_row091 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow20.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (237/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow20 window20_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row091_pos hδ hp) hR
theorem envelope_row092 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow21.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow21 window21_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row092_pos hδ hp) hR
theorem envelope_row093 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow22.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow22 window22_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row093_pos hδ hp) hR
theorem envelope_row094 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow23.Available δ p := by
  change δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow23 window23_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row094_pos hδ hp) hR
theorem envelope_row095 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow24.Available δ p := by
  change δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow24 window24_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row095_pos hδ hp) hR
theorem envelope_row096 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row096_pos hδ hp) hR
theorem envelope_row097 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row097_pos hδ hp) hR
theorem envelope_row098 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow27.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow27 window27_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row098_pos hδ hp) hR
theorem envelope_row099 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow28.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow28 window28_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row099_pos hδ hp) hR
theorem envelope_row100 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow29.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow29 window29_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row100_pos hδ hp) hR
theorem envelope_row101 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow30.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow30 window30_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row101_pos hδ hp) hR
theorem envelope_row102 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow31.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow31 window31_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row102_pos hδ hp) hR
theorem envelope_row103 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row103_pos hδ hp) hR
theorem envelope_row104 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row104_pos hδ hp) hR
theorem envelope_row105 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row105_pos hδ hp) hR
theorem envelope_row106 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row106_pos hδ hp) hR
theorem envelope_row107 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row107_pos hδ hp) hR
theorem envelope_row108 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row108_pos hδ hp) hR
theorem envelope_row109 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row109_pos hδ hp) hR
theorem envelope_row110 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow04.Available δ p := by
  change δ∈Set.Icc (3/8:ℝ) (27/64:ℝ) ∧ p∈Set.Icc (7/16:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow04 window04_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row110_pos hδ hp) hR
theorem envelope_row111 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row111_pos hδ hp) hR
theorem envelope_row112 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow06.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capP δ p/countJ .capP δ p := finiteEnvelope_le_window returnWindow06 window06_mem ha
 exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row112_pos hδ hp) hR
theorem envelope_row113 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow07.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (111/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow07 window07_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row113_pos hδ hp) hR
theorem envelope_row114 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow08.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC8 δ p/countJ .weakC8 δ p := finiteEnvelope_le_window returnWindow08 window08_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC8 hd0 hp0) (row114_pos hδ hp) hR
theorem envelope_row115 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow09.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC6 δ p/countJ .weakC6 δ p := finiteEnvelope_le_window returnWindow09 window09_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC6 hd0 hp0) (row115_pos hδ hp) hR
theorem envelope_row116 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow10.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC2 δ p/countJ .weakC2 δ p := finiteEnvelope_le_window returnWindow10 window10_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC2 hd0 hp0) (row116_pos hδ hp) hR
theorem envelope_row117 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow11.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow11 window11_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row117_pos hδ hp) hR
theorem envelope_row118 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow12.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow12 window12_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row118_pos hδ hp) hR
theorem envelope_row119 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow13.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow13 window13_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row119_pos hδ hp) hR
theorem envelope_row120 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow14.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (255/512:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow14 window14_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row120_pos hδ hp) hR
theorem envelope_row121 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow15.Available δ p := by
  change δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow15 window15_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row121_pos hδ hp) hR
theorem envelope_row122 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow16.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow16 window16_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row122_pos hδ hp) hR
theorem envelope_row123 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow17.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow17 window17_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row123_pos hδ hp) hR
theorem envelope_row124 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow18.Available δ p := by
  change δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow18 window18_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row124_pos hδ hp) hR
theorem envelope_row125 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow19.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow19 window19_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row125_pos hδ hp) hR
theorem envelope_row126 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow20.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (237/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow20 window20_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row126_pos hδ hp) hR
theorem envelope_row127 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow21.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow21 window21_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row127_pos hδ hp) hR
theorem envelope_row128 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow22.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow22 window22_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row128_pos hδ hp) hR
theorem envelope_row129 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow23.Available δ p := by
  change δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow23 window23_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row129_pos hδ hp) hR
theorem envelope_row130 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow24.Available δ p := by
  change δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow24 window24_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row130_pos hδ hp) hR
theorem envelope_row131 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row131_pos hδ hp) hR
theorem envelope_row132 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row132_pos hδ hp) hR
theorem envelope_row133 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow27.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow27 window27_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row133_pos hδ hp) hR
theorem envelope_row134 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow28.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow28 window28_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row134_pos hδ hp) hR
theorem envelope_row135 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow29.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow29 window29_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row135_pos hδ hp) hR
theorem envelope_row136 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow30.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow30 window30_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row136_pos hδ hp) hR
theorem envelope_row137 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow31.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow31 window31_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row137_pos hδ hp) hR
theorem envelope_row138 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row138_pos hδ hp) hR
theorem envelope_row139 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row139_pos hδ hp) hR
theorem envelope_row140 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row140_pos hδ hp) hR
theorem envelope_row141 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row141_pos hδ hp) hR
theorem envelope_row142 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row142_pos hδ hp) hR
theorem envelope_row143 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row143_pos hδ hp) hR
theorem envelope_row144 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row144_pos hδ hp) hR
theorem envelope_row145 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow04.Available δ p := by
  change δ∈Set.Icc (3/8:ℝ) (27/64:ℝ) ∧ p∈Set.Icc (7/16:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow04 window04_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row145_pos hδ hp) hR
theorem envelope_row146 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row146_pos hδ hp) hR
theorem envelope_row147 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow06.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capP δ p/countJ .capP δ p := finiteEnvelope_le_window returnWindow06 window06_mem ha
 exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row147_pos hδ hp) hR
theorem envelope_row148 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow07.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (111/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow07 window07_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row148_pos hδ hp) hR
theorem envelope_row149 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow08.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC8 δ p/countJ .weakC8 δ p := finiteEnvelope_le_window returnWindow08 window08_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC8 hd0 hp0) (row149_pos hδ hp) hR
theorem envelope_row150 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow09.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC6 δ p/countJ .weakC6 δ p := finiteEnvelope_le_window returnWindow09 window09_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC6 hd0 hp0) (row150_pos hδ hp) hR
theorem envelope_row151 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow10.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC2 δ p/countJ .weakC2 δ p := finiteEnvelope_le_window returnWindow10 window10_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC2 hd0 hp0) (row151_pos hδ hp) hR
theorem envelope_row152 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow11.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow11 window11_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row152_pos hδ hp) hR
theorem envelope_row153 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow12.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow12 window12_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row153_pos hδ hp) hR
theorem envelope_row154 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow13.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow13 window13_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row154_pos hδ hp) hR
theorem envelope_row155 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow14.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (255/512:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow14 window14_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row155_pos hδ hp) hR
theorem envelope_row156 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow15.Available δ p := by
  change δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow15 window15_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row156_pos hδ hp) hR
theorem envelope_row157 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow16.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow16 window16_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row157_pos hδ hp) hR
theorem envelope_row158 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow17.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow17 window17_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row158_pos hδ hp) hR
theorem envelope_row159 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow18.Available δ p := by
  change δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow18 window18_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row159_pos hδ hp) hR
theorem envelope_row160 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow19.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow19 window19_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row160_pos hδ hp) hR
theorem envelope_row161 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow20.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (237/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow20 window20_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row161_pos hδ hp) hR
theorem envelope_row162 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow35.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow35 window35_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row162_pos hδ hp) hR
theorem envelope_row163 {δ p:ℝ} (hδ:δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow36.Available δ p := by
  change δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow36 window36_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row163_pos hδ hp) hR
theorem envelope_row164 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow21.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow21 window21_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row164_pos hδ hp) hR
theorem envelope_row165 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow22.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow22 window22_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row165_pos hδ hp) hR
theorem envelope_row166 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow23.Available δ p := by
  change δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow23 window23_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row166_pos hδ hp) hR
theorem envelope_row167 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow24.Available δ p := by
  change δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow24 window24_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row167_pos hδ hp) hR
theorem envelope_row168 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row168_pos hδ hp) hR
theorem envelope_row169 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row169_pos hδ hp) hR
theorem envelope_row170 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow27.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow27 window27_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row170_pos hδ hp) hR
theorem envelope_row171 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow28.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow28 window28_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row171_pos hδ hp) hR
theorem envelope_row172 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow29.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow29 window29_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row172_pos hδ hp) hR
theorem envelope_row173 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow30.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow30 window30_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row173_pos hδ hp) hR
theorem envelope_row174 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow31.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow31 window31_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row174_pos hδ hp) hR
theorem envelope_row175 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row175_pos hδ hp) hR
theorem envelope_row176 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row176_pos hδ hp) hR
theorem envelope_row177 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row177_pos hδ hp) hR
theorem envelope_row178 {δ p:ℝ} (hδ:δ∈Set.Icc (0:ℝ) (3/8:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row178_pos hδ hp) hR
theorem envelope_row179 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (0:ℝ) (1/4:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row179_pos hδ hp) hR
theorem envelope_row180 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row180_pos hδ hp) hR
theorem envelope_row181 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row181_pos hδ hp) hR
theorem envelope_row182 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow04.Available δ p := by
  change δ∈Set.Icc (3/8:ℝ) (27/64:ℝ) ∧ p∈Set.Icc (7/16:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow04 window04_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row182_pos hδ hp) hR
theorem envelope_row183 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row183_pos hδ hp) hR
theorem envelope_row184 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow06.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capP δ p/countJ .capP δ p := finiteEnvelope_le_window returnWindow06 window06_mem ha
 exact exponent_lt_of_margin (countJ_pos .capP hd0 hp0) (row184_pos hδ hp) hR
theorem envelope_row185 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow07.Available δ p := by
  change δ∈Set.Icc (27/64:ℝ) (111/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .capC δ p/countJ .capC δ p := finiteEnvelope_le_window returnWindow07 window07_mem ha
 exact exponent_lt_of_margin (countJ_pos .capC hd0 hp0) (row185_pos hδ hp) hR
theorem envelope_row186 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow08.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC8 δ p/countJ .weakC8 δ p := finiteEnvelope_le_window returnWindow08 window08_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC8 hd0 hp0) (row186_pos hδ hp) hR
theorem envelope_row187 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow09.Available δ p := by
  change δ∈Set.Icc (111/256:ℝ) (57/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC6 δ p/countJ .weakC6 δ p := finiteEnvelope_le_window returnWindow09 window09_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC6 hd0 hp0) (row187_pos hδ hp) hR
theorem envelope_row188 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow10.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .weakC2 δ p/countJ .weakC2 δ p := finiteEnvelope_le_window returnWindow10 window10_mem ha
 exact exponent_lt_of_margin (countJ_pos .weakC2 hd0 hp0) (row188_pos hδ hp) hR
theorem envelope_row189 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow11.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow11 window11_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row189_pos hδ hp) hR
theorem envelope_row190 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow12.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow12 window12_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row190_pos hδ hp) hR
theorem envelope_row191 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow13.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow13 window13_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row191_pos hδ hp) hR
theorem envelope_row192 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow14.Available δ p := by
  change δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ) ∧ p∈Set.Icc (255/512:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow14 window14_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row192_pos hδ hp) hR
theorem envelope_row193 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow15.Available δ p := by
  change δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow15 window15_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row193_pos hδ hp) hR
theorem envelope_row194 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow16.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow16 window16_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row194_pos hδ hp) hR
theorem envelope_row195 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow17.Available δ p := by
  change δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow17 window17_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row195_pos hδ hp) hR
theorem envelope_row196 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow18.Available δ p := by
  change δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow18 window18_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row196_pos hδ hp) hR
theorem envelope_row197 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow19.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow19 window19_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row197_pos hδ hp) hR
theorem envelope_row198 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow20.Available δ p := by
  change δ∈Set.Icc (117/256:ℝ) (237/512:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow20 window20_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row198_pos hδ hp) hR
theorem envelope_row199 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow21.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow21 window21_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row199_pos hδ hp) hR
theorem envelope_row200 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow22.Available δ p := by
  change δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow22 window22_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row200_pos hδ hp) hR
theorem envelope_row201 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow23.Available δ p := by
  change δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ) ∧ p∈Set.Icc (127/256:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow23 window23_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row201_pos hδ hp) hR
theorem envelope_row202 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow24.Available δ p := by
  change δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow24 window24_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row202_pos hδ hp) hR
theorem envelope_row203 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row203_pos hδ hp) hR
theorem envelope_row204 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row204_pos hδ hp) hR
theorem envelope_row205 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow27.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (15/32:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow27 window27_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row205_pos hδ hp) hR
theorem envelope_row206 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow28.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow28 window28_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row206_pos hδ hp) hR
theorem envelope_row207 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow29.Available δ p := by
  change δ∈Set.Icc (15/32:ℝ) (123/256:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .C δ p/countJ .C δ p := finiteEnvelope_le_window returnWindow29 window29_mem ha
 exact exponent_lt_of_margin (countJ_pos .C hd0 hp0) (row207_pos hδ hp) hR
theorem envelope_row208 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow30.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (31/64:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow30 window30_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row208_pos hδ hp) hR
theorem envelope_row209 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ)) (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have ha : returnWindow31.Available δ p := by
  change δ∈Set.Icc (123/256:ℝ) (63/128:ℝ) ∧ p∈Set.Icc (63/128:ℝ) (1/2:ℝ)
  constructor <;> constructor <;> linarith [hδ.1,hδ.2,hp.1,hp.2]
 have hR : @GenericCount.envelope countScheme kappa δ p≤countN .P δ p/countJ .P δ p := finiteEnvelope_le_window returnWindow31 window31_mem ha
 exact exponent_lt_of_margin (countJ_pos .P hd0 hp0) (row209_pos hδ hp) hR
theorem envelope_row210 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ)) (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row210_pos hδ hp) hR
theorem envelope_row211 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ)) (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row211_pos hδ hp) hR
theorem envelope_row212 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ)) (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 have hd0 : δ∈Set.Icc 0 (3/4) := by constructor <;> linarith [hδ.1,hδ.2]
 have hp0 : p∈Set.Icc 0 (1/2) := by constructor <;> linarith [hp.1,hp.2]
 have hR := finiteEnvelope_le_old hd0 hp0
 exact exponent_lt_of_margin (countJ_pos .old hd0 hp0) (row212_pos hδ hp) hR
theorem cover_node_0 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row001 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_1 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row002 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_2 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row003 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_3 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row004 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_4 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row026 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_5 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_3 ⟨hδ.1,hs⟩ hp
 · exact cover_node_4 ⟨hs,hδ.2⟩ hp
theorem cover_node_6 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (3/8:ℝ) with hs | hs
 · exact cover_node_2 hδ ⟨hp.1,hs⟩
 · exact cover_node_5 hδ ⟨hs,hp.2⟩
theorem cover_node_7 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row005 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_8 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row006 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_9 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row007 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_10 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row011 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_11 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_9 ⟨hδ.1,hs⟩ hp
 · exact cover_node_10 ⟨hs,hδ.2⟩ hp
theorem cover_node_12 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_8 hδ ⟨hp.1,hs⟩
 · exact cover_node_11 hδ ⟨hs,hp.2⟩
theorem cover_node_13 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row008 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_14 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row009 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_15 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row010 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_16 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_14 hδ ⟨hp.1,hs⟩
 · exact cover_node_15 hδ ⟨hs,hp.2⟩
theorem cover_node_17 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (111/256:ℝ) with hs | hs
 · exact cover_node_13 ⟨hδ.1,hs⟩ hp
 · exact cover_node_16 ⟨hs,hδ.2⟩ hp
theorem cover_node_18 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row012 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_19 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row013 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_20 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row017 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_21 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_19 ⟨hδ.1,hs⟩ hp
 · exact cover_node_20 ⟨hs,hδ.2⟩ hp
theorem cover_node_22 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_18 hδ ⟨hp.1,hs⟩
 · exact cover_node_21 hδ ⟨hs,hp.2⟩
theorem cover_node_23 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row014 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_24 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row015 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_25 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (255/512:ℝ) with hs | hs
 · exact cover_node_23 hδ ⟨hp.1,hs⟩
 · exact cover_node_24 hδ ⟨hs,hp.2⟩
theorem cover_node_26 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row016 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_27 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row018 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_28 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row019 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_29 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (465/1024:ℝ) with hs | hs
 · exact cover_node_27 ⟨hδ.1,hs⟩ hp
 · exact cover_node_28 ⟨hs,hδ.2⟩ hp
theorem cover_node_30 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_26 ⟨hδ.1,hs⟩ hp
 · exact cover_node_29 ⟨hs,hδ.2⟩ hp
theorem cover_node_31 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (459/1024:ℝ) with hs | hs
 · exact cover_node_25 ⟨hδ.1,hs⟩ hp
 · exact cover_node_30 ⟨hs,hδ.2⟩ hp
theorem cover_node_32 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_22 hδ ⟨hp.1,hs⟩
 · exact cover_node_31 hδ ⟨hs,hp.2⟩
theorem cover_node_33 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_17 ⟨hδ.1,hs⟩ hp
 · exact cover_node_32 ⟨hs,hδ.2⟩ hp
theorem cover_node_34 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row020 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_35 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row021 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_36 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row022 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_37 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row023 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_38 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row024 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_39 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (951/2048:ℝ) with hs | hs
 · exact cover_node_37 ⟨hδ.1,hs⟩ hp
 · exact cover_node_38 ⟨hs,hδ.2⟩ hp
theorem cover_node_40 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_36 hδ ⟨hp.1,hs⟩
 · exact cover_node_39 hδ ⟨hs,hp.2⟩
theorem cover_node_41 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row025 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_42 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (477/1024:ℝ) with hs | hs
 · exact cover_node_40 ⟨hδ.1,hs⟩ hp
 · exact cover_node_41 ⟨hs,hδ.2⟩ hp
theorem cover_node_43 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (237/512:ℝ) with hs | hs
 · exact cover_node_35 ⟨hδ.1,hs⟩ hp
 · exact cover_node_42 ⟨hs,hδ.2⟩ hp
theorem cover_node_44 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_34 hδ ⟨hp.1,hs⟩
 · exact cover_node_43 hδ ⟨hs,hp.2⟩
theorem cover_node_45 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (117/256:ℝ) with hs | hs
 · exact cover_node_33 ⟨hδ.1,hs⟩ hp
 · exact cover_node_44 ⟨hs,hδ.2⟩ hp
theorem cover_node_46 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_12 hδ ⟨hp.1,hs⟩
 · exact cover_node_45 hδ ⟨hs,hp.2⟩
theorem cover_node_47 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (27/64:ℝ) with hs | hs
 · exact cover_node_7 ⟨hδ.1,hs⟩ hp
 · exact cover_node_46 ⟨hs,hδ.2⟩ hp
theorem cover_node_48 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row027 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_49 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row028 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_50 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row029 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_51 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row031 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_52 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_50 ⟨hδ.1,hs⟩ hp
 · exact cover_node_51 ⟨hs,hδ.2⟩ hp
theorem cover_node_53 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_49 hδ ⟨hp.1,hs⟩
 · exact cover_node_52 hδ ⟨hs,hp.2⟩
theorem cover_node_54 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row030 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_55 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row032 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_56 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_54 ⟨hδ.1,hs⟩ hp
 · exact cover_node_55 ⟨hs,hδ.2⟩ hp
theorem cover_node_57 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_53 hδ ⟨hp.1,hs⟩
 · exact cover_node_56 hδ ⟨hs,hp.2⟩
theorem cover_node_58 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row033 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_59 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (63/128:ℝ) with hs | hs
 · exact cover_node_57 ⟨hδ.1,hs⟩ hp
 · exact cover_node_58 ⟨hs,hδ.2⟩ hp
theorem cover_node_60 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_48 hδ ⟨hp.1,hs⟩
 · exact cover_node_59 hδ ⟨hs,hp.2⟩
theorem cover_node_61 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row034 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_62 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (33/64:ℝ) with hs | hs
 · exact cover_node_60 ⟨hδ.1,hs⟩ hp
 · exact cover_node_61 ⟨hs,hδ.2⟩ hp
theorem cover_node_63 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_47 ⟨hδ.1,hs⟩ hp
 · exact cover_node_62 ⟨hs,hδ.2⟩ hp
theorem cover_node_64 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (7/16:ℝ) with hs | hs
 · exact cover_node_6 hδ ⟨hp.1,hs⟩
 · exact cover_node_63 hδ ⟨hs,hp.2⟩
theorem cover_node_65 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row035 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_66 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (9/16:ℝ) with hs | hs
 · exact cover_node_64 ⟨hδ.1,hs⟩ hp
 · exact cover_node_65 ⟨hs,hδ.2⟩ hp
theorem cover_node_67 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (1/4:ℝ) with hs | hs
 · exact cover_node_1 hδ ⟨hp.1,hs⟩
 · exact cover_node_66 hδ ⟨hs,hp.2⟩
theorem cover_node_68 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hs | hs
 · exact cover_node_0 ⟨hδ.1,hs⟩ hp
 · exact cover_node_67 ⟨hs,hδ.2⟩ hp
theorem edge_oldSmall_certificate {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
 (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD .oldSmall) (edgeC .oldSmall) δ p+3/4*edgeD .oldSmall*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact cover_node_68 (by simpa using hδ) (by simpa using hp)
theorem cover_node_69 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row036 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_70 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row037 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_71 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row038 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_72 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row039 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_73 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row061 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_74 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_72 ⟨hδ.1,hs⟩ hp
 · exact cover_node_73 ⟨hs,hδ.2⟩ hp
theorem cover_node_75 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (3/8:ℝ) with hs | hs
 · exact cover_node_71 hδ ⟨hp.1,hs⟩
 · exact cover_node_74 hδ ⟨hs,hp.2⟩
theorem cover_node_76 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row040 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_77 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row041 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_78 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row042 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_79 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row046 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_80 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_78 ⟨hδ.1,hs⟩ hp
 · exact cover_node_79 ⟨hs,hδ.2⟩ hp
theorem cover_node_81 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_77 hδ ⟨hp.1,hs⟩
 · exact cover_node_80 hδ ⟨hs,hp.2⟩
theorem cover_node_82 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row043 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_83 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row044 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_84 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row045 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_85 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_83 hδ ⟨hp.1,hs⟩
 · exact cover_node_84 hδ ⟨hs,hp.2⟩
theorem cover_node_86 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (111/256:ℝ) with hs | hs
 · exact cover_node_82 ⟨hδ.1,hs⟩ hp
 · exact cover_node_85 ⟨hs,hδ.2⟩ hp
theorem cover_node_87 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row047 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_88 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row048 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_89 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row052 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_90 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_88 ⟨hδ.1,hs⟩ hp
 · exact cover_node_89 ⟨hs,hδ.2⟩ hp
theorem cover_node_91 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_87 hδ ⟨hp.1,hs⟩
 · exact cover_node_90 hδ ⟨hs,hp.2⟩
theorem cover_node_92 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row049 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_93 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row050 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_94 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (255/512:ℝ) with hs | hs
 · exact cover_node_92 hδ ⟨hp.1,hs⟩
 · exact cover_node_93 hδ ⟨hs,hp.2⟩
theorem cover_node_95 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row051 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_96 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row053 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_97 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row054 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_98 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (465/1024:ℝ) with hs | hs
 · exact cover_node_96 ⟨hδ.1,hs⟩ hp
 · exact cover_node_97 ⟨hs,hδ.2⟩ hp
theorem cover_node_99 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_95 ⟨hδ.1,hs⟩ hp
 · exact cover_node_98 ⟨hs,hδ.2⟩ hp
theorem cover_node_100 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (459/1024:ℝ) with hs | hs
 · exact cover_node_94 ⟨hδ.1,hs⟩ hp
 · exact cover_node_99 ⟨hs,hδ.2⟩ hp
theorem cover_node_101 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_91 hδ ⟨hp.1,hs⟩
 · exact cover_node_100 hδ ⟨hs,hp.2⟩
theorem cover_node_102 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_86 ⟨hδ.1,hs⟩ hp
 · exact cover_node_101 ⟨hs,hδ.2⟩ hp
theorem cover_node_103 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row055 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_104 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row056 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_105 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row057 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_106 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row058 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_107 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row059 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_108 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (951/2048:ℝ) with hs | hs
 · exact cover_node_106 ⟨hδ.1,hs⟩ hp
 · exact cover_node_107 ⟨hs,hδ.2⟩ hp
theorem cover_node_109 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_105 hδ ⟨hp.1,hs⟩
 · exact cover_node_108 hδ ⟨hs,hp.2⟩
theorem cover_node_110 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row060 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_111 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (477/1024:ℝ) with hs | hs
 · exact cover_node_109 ⟨hδ.1,hs⟩ hp
 · exact cover_node_110 ⟨hs,hδ.2⟩ hp
theorem cover_node_112 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (237/512:ℝ) with hs | hs
 · exact cover_node_104 ⟨hδ.1,hs⟩ hp
 · exact cover_node_111 ⟨hs,hδ.2⟩ hp
theorem cover_node_113 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_103 hδ ⟨hp.1,hs⟩
 · exact cover_node_112 hδ ⟨hs,hp.2⟩
theorem cover_node_114 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (117/256:ℝ) with hs | hs
 · exact cover_node_102 ⟨hδ.1,hs⟩ hp
 · exact cover_node_113 ⟨hs,hδ.2⟩ hp
theorem cover_node_115 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_81 hδ ⟨hp.1,hs⟩
 · exact cover_node_114 hδ ⟨hs,hp.2⟩
theorem cover_node_116 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (27/64:ℝ) with hs | hs
 · exact cover_node_76 ⟨hδ.1,hs⟩ hp
 · exact cover_node_115 ⟨hs,hδ.2⟩ hp
theorem cover_node_117 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row062 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_118 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row063 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_119 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row064 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_120 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row066 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_121 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_119 ⟨hδ.1,hs⟩ hp
 · exact cover_node_120 ⟨hs,hδ.2⟩ hp
theorem cover_node_122 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_118 hδ ⟨hp.1,hs⟩
 · exact cover_node_121 hδ ⟨hs,hp.2⟩
theorem cover_node_123 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row065 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_124 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row067 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_125 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_123 ⟨hδ.1,hs⟩ hp
 · exact cover_node_124 ⟨hs,hδ.2⟩ hp
theorem cover_node_126 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_122 hδ ⟨hp.1,hs⟩
 · exact cover_node_125 hδ ⟨hs,hp.2⟩
theorem cover_node_127 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row068 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_128 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (63/128:ℝ) with hs | hs
 · exact cover_node_126 ⟨hδ.1,hs⟩ hp
 · exact cover_node_127 ⟨hs,hδ.2⟩ hp
theorem cover_node_129 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_117 hδ ⟨hp.1,hs⟩
 · exact cover_node_128 hδ ⟨hs,hp.2⟩
theorem cover_node_130 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row069 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_131 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (33/64:ℝ) with hs | hs
 · exact cover_node_129 ⟨hδ.1,hs⟩ hp
 · exact cover_node_130 ⟨hs,hδ.2⟩ hp
theorem cover_node_132 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_116 ⟨hδ.1,hs⟩ hp
 · exact cover_node_131 ⟨hs,hδ.2⟩ hp
theorem cover_node_133 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (7/16:ℝ) with hs | hs
 · exact cover_node_75 hδ ⟨hp.1,hs⟩
 · exact cover_node_132 hδ ⟨hs,hp.2⟩
theorem cover_node_134 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row070 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_135 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (9/16:ℝ) with hs | hs
 · exact cover_node_133 ⟨hδ.1,hs⟩ hp
 · exact cover_node_134 ⟨hs,hδ.2⟩ hp
theorem cover_node_136 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (1/4:ℝ) with hs | hs
 · exact cover_node_70 hδ ⟨hp.1,hs⟩
 · exact cover_node_135 hδ ⟨hs,hp.2⟩
theorem cover_node_137 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hs | hs
 · exact cover_node_69 ⟨hδ.1,hs⟩ hp
 · exact cover_node_136 ⟨hs,hδ.2⟩ hp
theorem edge_oldPeak_certificate {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
 (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD .oldPeak) (edgeC .oldPeak) δ p+3/4*edgeD .oldPeak*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact cover_node_137 (by simpa using hδ) (by simpa using hp)
theorem cover_node_138 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row071 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_139 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row072 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_140 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row073 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_141 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row074 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_142 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row096 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_143 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_141 ⟨hδ.1,hs⟩ hp
 · exact cover_node_142 ⟨hs,hδ.2⟩ hp
theorem cover_node_144 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (7/16:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (3/8:ℝ) with hs | hs
 · exact cover_node_140 hδ ⟨hp.1,hs⟩
 · exact cover_node_143 hδ ⟨hs,hp.2⟩
theorem cover_node_145 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row075 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_146 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row076 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_147 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row077 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_148 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row081 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_149 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_147 ⟨hδ.1,hs⟩ hp
 · exact cover_node_148 ⟨hs,hδ.2⟩ hp
theorem cover_node_150 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_146 hδ ⟨hp.1,hs⟩
 · exact cover_node_149 hδ ⟨hs,hp.2⟩
theorem cover_node_151 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row078 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_152 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row079 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_153 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row080 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_154 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_152 hδ ⟨hp.1,hs⟩
 · exact cover_node_153 hδ ⟨hs,hp.2⟩
theorem cover_node_155 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (111/256:ℝ) with hs | hs
 · exact cover_node_151 ⟨hδ.1,hs⟩ hp
 · exact cover_node_154 ⟨hs,hδ.2⟩ hp
theorem cover_node_156 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row082 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_157 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row083 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_158 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row087 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_159 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_157 ⟨hδ.1,hs⟩ hp
 · exact cover_node_158 ⟨hs,hδ.2⟩ hp
theorem cover_node_160 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_156 hδ ⟨hp.1,hs⟩
 · exact cover_node_159 hδ ⟨hs,hp.2⟩
theorem cover_node_161 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row084 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_162 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row085 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_163 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (255/512:ℝ) with hs | hs
 · exact cover_node_161 hδ ⟨hp.1,hs⟩
 · exact cover_node_162 hδ ⟨hs,hp.2⟩
theorem cover_node_164 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row086 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_165 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row088 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_166 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row089 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_167 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (465/1024:ℝ) with hs | hs
 · exact cover_node_165 ⟨hδ.1,hs⟩ hp
 · exact cover_node_166 ⟨hs,hδ.2⟩ hp
theorem cover_node_168 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_164 ⟨hδ.1,hs⟩ hp
 · exact cover_node_167 ⟨hs,hδ.2⟩ hp
theorem cover_node_169 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (459/1024:ℝ) with hs | hs
 · exact cover_node_163 ⟨hδ.1,hs⟩ hp
 · exact cover_node_168 ⟨hs,hδ.2⟩ hp
theorem cover_node_170 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_160 hδ ⟨hp.1,hs⟩
 · exact cover_node_169 hδ ⟨hs,hp.2⟩
theorem cover_node_171 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_155 ⟨hδ.1,hs⟩ hp
 · exact cover_node_170 ⟨hs,hδ.2⟩ hp
theorem cover_node_172 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row090 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_173 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row091 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_174 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row092 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_175 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row093 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_176 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row094 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_177 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (951/2048:ℝ) with hs | hs
 · exact cover_node_175 ⟨hδ.1,hs⟩ hp
 · exact cover_node_176 ⟨hs,hδ.2⟩ hp
theorem cover_node_178 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_174 hδ ⟨hp.1,hs⟩
 · exact cover_node_177 hδ ⟨hs,hp.2⟩
theorem cover_node_179 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row095 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_180 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (477/1024:ℝ) with hs | hs
 · exact cover_node_178 ⟨hδ.1,hs⟩ hp
 · exact cover_node_179 ⟨hs,hδ.2⟩ hp
theorem cover_node_181 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (237/512:ℝ) with hs | hs
 · exact cover_node_173 ⟨hδ.1,hs⟩ hp
 · exact cover_node_180 ⟨hs,hδ.2⟩ hp
theorem cover_node_182 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_172 hδ ⟨hp.1,hs⟩
 · exact cover_node_181 hδ ⟨hs,hp.2⟩
theorem cover_node_183 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (117/256:ℝ) with hs | hs
 · exact cover_node_171 ⟨hδ.1,hs⟩ hp
 · exact cover_node_182 ⟨hs,hδ.2⟩ hp
theorem cover_node_184 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_150 hδ ⟨hp.1,hs⟩
 · exact cover_node_183 hδ ⟨hs,hp.2⟩
theorem cover_node_185 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (27/64:ℝ) with hs | hs
 · exact cover_node_145 ⟨hδ.1,hs⟩ hp
 · exact cover_node_184 ⟨hs,hδ.2⟩ hp
theorem cover_node_186 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row097 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_187 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row098 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_188 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row099 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_189 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row101 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_190 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_188 ⟨hδ.1,hs⟩ hp
 · exact cover_node_189 ⟨hs,hδ.2⟩ hp
theorem cover_node_191 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_187 hδ ⟨hp.1,hs⟩
 · exact cover_node_190 hδ ⟨hs,hp.2⟩
theorem cover_node_192 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row100 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_193 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row102 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_194 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_192 ⟨hδ.1,hs⟩ hp
 · exact cover_node_193 ⟨hs,hδ.2⟩ hp
theorem cover_node_195 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_191 hδ ⟨hp.1,hs⟩
 · exact cover_node_194 hδ ⟨hs,hp.2⟩
theorem cover_node_196 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row103 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_197 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (63/128:ℝ) with hs | hs
 · exact cover_node_195 ⟨hδ.1,hs⟩ hp
 · exact cover_node_196 ⟨hs,hδ.2⟩ hp
theorem cover_node_198 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_186 hδ ⟨hp.1,hs⟩
 · exact cover_node_197 hδ ⟨hs,hp.2⟩
theorem cover_node_199 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row104 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_200 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (33/64:ℝ) with hs | hs
 · exact cover_node_198 ⟨hδ.1,hs⟩ hp
 · exact cover_node_199 ⟨hs,hδ.2⟩ hp
theorem cover_node_201 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_185 ⟨hδ.1,hs⟩ hp
 · exact cover_node_200 ⟨hs,hδ.2⟩ hp
theorem cover_node_202 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (7/16:ℝ) with hs | hs
 · exact cover_node_144 hδ ⟨hp.1,hs⟩
 · exact cover_node_201 hδ ⟨hs,hp.2⟩
theorem cover_node_203 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row105 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_204 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (9/16:ℝ) with hs | hs
 · exact cover_node_202 ⟨hδ.1,hs⟩ hp
 · exact cover_node_203 ⟨hs,hδ.2⟩ hp
theorem cover_node_205 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (1/4:ℝ) with hs | hs
 · exact cover_node_139 hδ ⟨hp.1,hs⟩
 · exact cover_node_204 hδ ⟨hs,hp.2⟩
theorem cover_node_206 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hs | hs
 · exact cover_node_138 ⟨hδ.1,hs⟩ hp
 · exact cover_node_205 ⟨hs,hδ.2⟩ hp
theorem edge_oldSwitch_certificate {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
 (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD .oldSwitch) (edgeC .oldSwitch) δ p+3/4*edgeD .oldSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact cover_node_206 (by simpa using hδ) (by simpa using hp)
theorem cover_node_207 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row106 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_208 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row107 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_209 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row108 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_210 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row109 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_211 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row131 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_212 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_210 ⟨hδ.1,hs⟩ hp
 · exact cover_node_211 ⟨hs,hδ.2⟩ hp
theorem cover_node_213 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (7/16:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (3/8:ℝ) with hs | hs
 · exact cover_node_209 hδ ⟨hp.1,hs⟩
 · exact cover_node_212 hδ ⟨hs,hp.2⟩
theorem cover_node_214 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row110 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_215 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row111 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_216 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row112 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_217 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row116 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_218 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_216 ⟨hδ.1,hs⟩ hp
 · exact cover_node_217 ⟨hs,hδ.2⟩ hp
theorem cover_node_219 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_215 hδ ⟨hp.1,hs⟩
 · exact cover_node_218 hδ ⟨hs,hp.2⟩
theorem cover_node_220 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row113 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_221 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row114 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_222 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row115 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_223 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_221 hδ ⟨hp.1,hs⟩
 · exact cover_node_222 hδ ⟨hs,hp.2⟩
theorem cover_node_224 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (111/256:ℝ) with hs | hs
 · exact cover_node_220 ⟨hδ.1,hs⟩ hp
 · exact cover_node_223 ⟨hs,hδ.2⟩ hp
theorem cover_node_225 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row117 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_226 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row118 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_227 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row122 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_228 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_226 ⟨hδ.1,hs⟩ hp
 · exact cover_node_227 ⟨hs,hδ.2⟩ hp
theorem cover_node_229 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_225 hδ ⟨hp.1,hs⟩
 · exact cover_node_228 hδ ⟨hs,hp.2⟩
theorem cover_node_230 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row119 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_231 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row120 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_232 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (255/512:ℝ) with hs | hs
 · exact cover_node_230 hδ ⟨hp.1,hs⟩
 · exact cover_node_231 hδ ⟨hs,hp.2⟩
theorem cover_node_233 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row121 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_234 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row123 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_235 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row124 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_236 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (465/1024:ℝ) with hs | hs
 · exact cover_node_234 ⟨hδ.1,hs⟩ hp
 · exact cover_node_235 ⟨hs,hδ.2⟩ hp
theorem cover_node_237 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_233 ⟨hδ.1,hs⟩ hp
 · exact cover_node_236 ⟨hs,hδ.2⟩ hp
theorem cover_node_238 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (459/1024:ℝ) with hs | hs
 · exact cover_node_232 ⟨hδ.1,hs⟩ hp
 · exact cover_node_237 ⟨hs,hδ.2⟩ hp
theorem cover_node_239 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_229 hδ ⟨hp.1,hs⟩
 · exact cover_node_238 hδ ⟨hs,hp.2⟩
theorem cover_node_240 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_224 ⟨hδ.1,hs⟩ hp
 · exact cover_node_239 ⟨hs,hδ.2⟩ hp
theorem cover_node_241 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row125 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_242 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row126 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_243 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row127 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_244 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row128 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_245 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row129 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_246 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (951/2048:ℝ) with hs | hs
 · exact cover_node_244 ⟨hδ.1,hs⟩ hp
 · exact cover_node_245 ⟨hs,hδ.2⟩ hp
theorem cover_node_247 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_243 hδ ⟨hp.1,hs⟩
 · exact cover_node_246 hδ ⟨hs,hp.2⟩
theorem cover_node_248 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row130 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_249 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (477/1024:ℝ) with hs | hs
 · exact cover_node_247 ⟨hδ.1,hs⟩ hp
 · exact cover_node_248 ⟨hs,hδ.2⟩ hp
theorem cover_node_250 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (237/512:ℝ) with hs | hs
 · exact cover_node_242 ⟨hδ.1,hs⟩ hp
 · exact cover_node_249 ⟨hs,hδ.2⟩ hp
theorem cover_node_251 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_241 hδ ⟨hp.1,hs⟩
 · exact cover_node_250 hδ ⟨hs,hp.2⟩
theorem cover_node_252 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (117/256:ℝ) with hs | hs
 · exact cover_node_240 ⟨hδ.1,hs⟩ hp
 · exact cover_node_251 ⟨hs,hδ.2⟩ hp
theorem cover_node_253 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_219 hδ ⟨hp.1,hs⟩
 · exact cover_node_252 hδ ⟨hs,hp.2⟩
theorem cover_node_254 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (27/64:ℝ) with hs | hs
 · exact cover_node_214 ⟨hδ.1,hs⟩ hp
 · exact cover_node_253 ⟨hs,hδ.2⟩ hp
theorem cover_node_255 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row132 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_256 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row133 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_257 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row134 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_258 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row136 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_259 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_257 ⟨hδ.1,hs⟩ hp
 · exact cover_node_258 ⟨hs,hδ.2⟩ hp
theorem cover_node_260 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_256 hδ ⟨hp.1,hs⟩
 · exact cover_node_259 hδ ⟨hs,hp.2⟩
theorem cover_node_261 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row135 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_262 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row137 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_263 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_261 ⟨hδ.1,hs⟩ hp
 · exact cover_node_262 ⟨hs,hδ.2⟩ hp
theorem cover_node_264 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_260 hδ ⟨hp.1,hs⟩
 · exact cover_node_263 hδ ⟨hs,hp.2⟩
theorem cover_node_265 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row138 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_266 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (63/128:ℝ) with hs | hs
 · exact cover_node_264 ⟨hδ.1,hs⟩ hp
 · exact cover_node_265 ⟨hs,hδ.2⟩ hp
theorem cover_node_267 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_255 hδ ⟨hp.1,hs⟩
 · exact cover_node_266 hδ ⟨hs,hp.2⟩
theorem cover_node_268 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row139 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_269 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (33/64:ℝ) with hs | hs
 · exact cover_node_267 ⟨hδ.1,hs⟩ hp
 · exact cover_node_268 ⟨hs,hδ.2⟩ hp
theorem cover_node_270 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_254 ⟨hδ.1,hs⟩ hp
 · exact cover_node_269 ⟨hs,hδ.2⟩ hp
theorem cover_node_271 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (7/16:ℝ) with hs | hs
 · exact cover_node_213 hδ ⟨hp.1,hs⟩
 · exact cover_node_270 hδ ⟨hs,hp.2⟩
theorem cover_node_272 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row140 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_273 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (9/16:ℝ) with hs | hs
 · exact cover_node_271 ⟨hδ.1,hs⟩ hp
 · exact cover_node_272 ⟨hs,hδ.2⟩ hp
theorem cover_node_274 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (1/4:ℝ) with hs | hs
 · exact cover_node_208 hδ ⟨hp.1,hs⟩
 · exact cover_node_273 hδ ⟨hs,hp.2⟩
theorem cover_node_275 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hs | hs
 · exact cover_node_207 ⟨hδ.1,hs⟩ hp
 · exact cover_node_274 ⟨hs,hδ.2⟩ hp
theorem edge_newSwitch_certificate {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
 (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD .newSwitch) (edgeC .newSwitch) δ p+3/4*edgeD .newSwitch*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact cover_node_275 (by simpa using hδ) (by simpa using hp)
theorem cover_node_276 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row141 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_277 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row142 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_278 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row143 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_279 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row144 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_280 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row168 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_281 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_279 ⟨hδ.1,hs⟩ hp
 · exact cover_node_280 ⟨hs,hδ.2⟩ hp
theorem cover_node_282 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (7/16:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (3/8:ℝ) with hs | hs
 · exact cover_node_278 hδ ⟨hp.1,hs⟩
 · exact cover_node_281 hδ ⟨hs,hp.2⟩
theorem cover_node_283 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row145 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_284 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row146 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_285 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row147 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_286 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row151 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_287 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_285 ⟨hδ.1,hs⟩ hp
 · exact cover_node_286 ⟨hs,hδ.2⟩ hp
theorem cover_node_288 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_284 hδ ⟨hp.1,hs⟩
 · exact cover_node_287 hδ ⟨hs,hp.2⟩
theorem cover_node_289 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row148 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_290 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row149 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_291 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row150 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_292 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_290 hδ ⟨hp.1,hs⟩
 · exact cover_node_291 hδ ⟨hs,hp.2⟩
theorem cover_node_293 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (111/256:ℝ) with hs | hs
 · exact cover_node_289 ⟨hδ.1,hs⟩ hp
 · exact cover_node_292 ⟨hs,hδ.2⟩ hp
theorem cover_node_294 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row152 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_295 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row153 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_296 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row157 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_297 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_295 ⟨hδ.1,hs⟩ hp
 · exact cover_node_296 ⟨hs,hδ.2⟩ hp
theorem cover_node_298 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_294 hδ ⟨hp.1,hs⟩
 · exact cover_node_297 hδ ⟨hs,hp.2⟩
theorem cover_node_299 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row154 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_300 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row155 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_301 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (255/512:ℝ) with hs | hs
 · exact cover_node_299 hδ ⟨hp.1,hs⟩
 · exact cover_node_300 hδ ⟨hs,hp.2⟩
theorem cover_node_302 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row156 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_303 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row158 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_304 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row159 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_305 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (465/1024:ℝ) with hs | hs
 · exact cover_node_303 ⟨hδ.1,hs⟩ hp
 · exact cover_node_304 ⟨hs,hδ.2⟩ hp
theorem cover_node_306 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_302 ⟨hδ.1,hs⟩ hp
 · exact cover_node_305 ⟨hs,hδ.2⟩ hp
theorem cover_node_307 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (459/1024:ℝ) with hs | hs
 · exact cover_node_301 ⟨hδ.1,hs⟩ hp
 · exact cover_node_306 ⟨hs,hδ.2⟩ hp
theorem cover_node_308 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_298 hδ ⟨hp.1,hs⟩
 · exact cover_node_307 hδ ⟨hs,hp.2⟩
theorem cover_node_309 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_293 ⟨hδ.1,hs⟩ hp
 · exact cover_node_308 ⟨hs,hδ.2⟩ hp
theorem cover_node_310 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row160 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_311 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row161 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_312 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row162 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_313 {δ p:ℝ} (hδ:δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row163 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_314 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (471/1024:ℝ) with hs | hs
 · exact cover_node_312 ⟨hδ.1,hs⟩ hp
 · exact cover_node_313 ⟨hs,hδ.2⟩ hp
theorem cover_node_315 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_311 hδ ⟨hp.1,hs⟩
 · exact cover_node_314 hδ ⟨hs,hp.2⟩
theorem cover_node_316 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row164 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_317 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row165 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_318 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row166 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_319 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (951/2048:ℝ) with hs | hs
 · exact cover_node_317 ⟨hδ.1,hs⟩ hp
 · exact cover_node_318 ⟨hs,hδ.2⟩ hp
theorem cover_node_320 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_316 hδ ⟨hp.1,hs⟩
 · exact cover_node_319 hδ ⟨hs,hp.2⟩
theorem cover_node_321 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row167 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_322 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (477/1024:ℝ) with hs | hs
 · exact cover_node_320 ⟨hδ.1,hs⟩ hp
 · exact cover_node_321 ⟨hs,hδ.2⟩ hp
theorem cover_node_323 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (237/512:ℝ) with hs | hs
 · exact cover_node_315 ⟨hδ.1,hs⟩ hp
 · exact cover_node_322 ⟨hs,hδ.2⟩ hp
theorem cover_node_324 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_310 hδ ⟨hp.1,hs⟩
 · exact cover_node_323 hδ ⟨hs,hp.2⟩
theorem cover_node_325 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (117/256:ℝ) with hs | hs
 · exact cover_node_309 ⟨hδ.1,hs⟩ hp
 · exact cover_node_324 ⟨hs,hδ.2⟩ hp
theorem cover_node_326 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_288 hδ ⟨hp.1,hs⟩
 · exact cover_node_325 hδ ⟨hs,hp.2⟩
theorem cover_node_327 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (27/64:ℝ) with hs | hs
 · exact cover_node_283 ⟨hδ.1,hs⟩ hp
 · exact cover_node_326 ⟨hs,hδ.2⟩ hp
theorem cover_node_328 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row169 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_329 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row170 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_330 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row171 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_331 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row173 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_332 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_330 ⟨hδ.1,hs⟩ hp
 · exact cover_node_331 ⟨hs,hδ.2⟩ hp
theorem cover_node_333 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_329 hδ ⟨hp.1,hs⟩
 · exact cover_node_332 hδ ⟨hs,hp.2⟩
theorem cover_node_334 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row172 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_335 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row174 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_336 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_334 ⟨hδ.1,hs⟩ hp
 · exact cover_node_335 ⟨hs,hδ.2⟩ hp
theorem cover_node_337 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_333 hδ ⟨hp.1,hs⟩
 · exact cover_node_336 hδ ⟨hs,hp.2⟩
theorem cover_node_338 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row175 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_339 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (63/128:ℝ) with hs | hs
 · exact cover_node_337 ⟨hδ.1,hs⟩ hp
 · exact cover_node_338 ⟨hs,hδ.2⟩ hp
theorem cover_node_340 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_328 hδ ⟨hp.1,hs⟩
 · exact cover_node_339 hδ ⟨hs,hp.2⟩
theorem cover_node_341 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row176 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_342 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (33/64:ℝ) with hs | hs
 · exact cover_node_340 ⟨hδ.1,hs⟩ hp
 · exact cover_node_341 ⟨hs,hδ.2⟩ hp
theorem cover_node_343 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_327 ⟨hδ.1,hs⟩ hp
 · exact cover_node_342 ⟨hs,hδ.2⟩ hp
theorem cover_node_344 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (7/16:ℝ) with hs | hs
 · exact cover_node_282 hδ ⟨hp.1,hs⟩
 · exact cover_node_343 hδ ⟨hs,hp.2⟩
theorem cover_node_345 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row177 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_346 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (9/16:ℝ) with hs | hs
 · exact cover_node_344 ⟨hδ.1,hs⟩ hp
 · exact cover_node_345 ⟨hs,hδ.2⟩ hp
theorem cover_node_347 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (1/4:ℝ) with hs | hs
 · exact cover_node_277 hδ ⟨hp.1,hs⟩
 · exact cover_node_346 hδ ⟨hs,hp.2⟩
theorem cover_node_348 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hs | hs
 · exact cover_node_276 ⟨hδ.1,hs⟩ hp
 · exact cover_node_347 ⟨hs,hδ.2⟩ hp
theorem edge_newTop_certificate {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
 (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD .newTop) (edgeC .newTop) δ p+3/4*edgeD .newTop*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact cover_node_348 (by simpa using hδ) (by simpa using hp)
theorem cover_node_349 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/8:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row178 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_350 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/4:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row179 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_351 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (3/8:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row180 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_352 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row181 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_353 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row203 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_354 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (3/8:ℝ) (7/16:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_352 ⟨hδ.1,hs⟩ hp
 · exact cover_node_353 ⟨hs,hδ.2⟩ hp
theorem cover_node_355 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (7/16:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (3/8:ℝ) with hs | hs
 · exact cover_node_351 hδ ⟨hp.1,hs⟩
 · exact cover_node_354 hδ ⟨hs,hp.2⟩
theorem cover_node_356 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row182 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_357 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row183 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_358 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row184 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_359 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row188 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_360 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_358 ⟨hδ.1,hs⟩ hp
 · exact cover_node_359 ⟨hs,hδ.2⟩ hp
theorem cover_node_361 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (31/64:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_357 hδ ⟨hp.1,hs⟩
 · exact cover_node_360 hδ ⟨hs,hp.2⟩
theorem cover_node_362 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row185 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_363 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row186 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_364 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row187 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_365 {δ p:ℝ} (hδ:δ∈Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_363 hδ ⟨hp.1,hs⟩
 · exact cover_node_364 hδ ⟨hs,hp.2⟩
theorem cover_node_366 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (111/256:ℝ) with hs | hs
 · exact cover_node_362 ⟨hδ.1,hs⟩ hp
 · exact cover_node_365 ⟨hs,hδ.2⟩ hp
theorem cover_node_367 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row189 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_368 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row190 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_369 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row194 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_370 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_368 ⟨hδ.1,hs⟩ hp
 · exact cover_node_369 ⟨hs,hδ.2⟩ hp
theorem cover_node_371 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (127/256:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_367 hδ ⟨hp.1,hs⟩
 · exact cover_node_370 hδ ⟨hs,hp.2⟩
theorem cover_node_372 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (255/512:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row191 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_373 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row192 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_374 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (255/512:ℝ) with hs | hs
 · exact cover_node_372 hδ ⟨hp.1,hs⟩
 · exact cover_node_373 hδ ⟨hs,hp.2⟩
theorem cover_node_375 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row193 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_376 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row195 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_377 {δ p:ℝ} (hδ:δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row196 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_378 {δ p:ℝ} (hδ:δ∈Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (465/1024:ℝ) with hs | hs
 · exact cover_node_376 ⟨hδ.1,hs⟩ hp
 · exact cover_node_377 ⟨hs,hδ.2⟩ hp
theorem cover_node_379 {δ p:ℝ} (hδ:δ∈Set.Icc (459/1024:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (231/512:ℝ) with hs | hs
 · exact cover_node_375 ⟨hδ.1,hs⟩ hp
 · exact cover_node_378 ⟨hs,hδ.2⟩ hp
theorem cover_node_380 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (459/1024:ℝ) with hs | hs
 · exact cover_node_374 ⟨hδ.1,hs⟩ hp
 · exact cover_node_379 ⟨hs,hδ.2⟩ hp
theorem cover_node_381 {δ p:ℝ} (hδ:δ∈Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_371 hδ ⟨hp.1,hs⟩
 · exact cover_node_380 hδ ⟨hs,hp.2⟩
theorem cover_node_382 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (117/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (57/128:ℝ) with hs | hs
 · exact cover_node_366 ⟨hδ.1,hs⟩ hp
 · exact cover_node_381 ⟨hs,hδ.2⟩ hp
theorem cover_node_383 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row197 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_384 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row198 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_385 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (127/256:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row199 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_386 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row200 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_387 {δ p:ℝ} (hδ:δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row201 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_388 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (951/2048:ℝ) with hs | hs
 · exact cover_node_386 ⟨hδ.1,hs⟩ hp
 · exact cover_node_387 ⟨hs,hδ.2⟩ hp
theorem cover_node_389 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (127/256:ℝ) with hs | hs
 · exact cover_node_385 hδ ⟨hp.1,hs⟩
 · exact cover_node_388 hδ ⟨hs,hp.2⟩
theorem cover_node_390 {δ p:ℝ} (hδ:δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row202 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_391 {δ p:ℝ} (hδ:δ∈Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (477/1024:ℝ) with hs | hs
 · exact cover_node_389 ⟨hδ.1,hs⟩ hp
 · exact cover_node_390 ⟨hs,hδ.2⟩ hp
theorem cover_node_392 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (237/512:ℝ) with hs | hs
 · exact cover_node_384 ⟨hδ.1,hs⟩ hp
 · exact cover_node_391 ⟨hs,hδ.2⟩ hp
theorem cover_node_393 {δ p:ℝ} (hδ:δ∈Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_383 hδ ⟨hp.1,hs⟩
 · exact cover_node_392 hδ ⟨hs,hp.2⟩
theorem cover_node_394 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (117/256:ℝ) with hs | hs
 · exact cover_node_382 ⟨hδ.1,hs⟩ hp
 · exact cover_node_393 ⟨hs,hδ.2⟩ hp
theorem cover_node_395 {δ p:ℝ} (hδ:δ∈Set.Icc (27/64:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_361 hδ ⟨hp.1,hs⟩
 · exact cover_node_394 hδ ⟨hs,hp.2⟩
theorem cover_node_396 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (27/64:ℝ) with hs | hs
 · exact cover_node_356 ⟨hδ.1,hs⟩ hp
 · exact cover_node_395 ⟨hs,hδ.2⟩ hp
theorem cover_node_397 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (15/32:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row204 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_398 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (31/64:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row205 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_399 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row206 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_400 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row208 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_401 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (31/64:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_399 ⟨hδ.1,hs⟩ hp
 · exact cover_node_400 ⟨hs,hδ.2⟩ hp
theorem cover_node_402 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (63/128:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (31/64:ℝ) with hs | hs
 · exact cover_node_398 hδ ⟨hp.1,hs⟩
 · exact cover_node_401 hδ ⟨hs,hp.2⟩
theorem cover_node_403 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row207 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_404 {δ p:ℝ} (hδ:δ∈Set.Icc (123/256:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row209 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_405 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (123/256:ℝ) with hs | hs
 · exact cover_node_403 ⟨hδ.1,hs⟩ hp
 · exact cover_node_404 ⟨hs,hδ.2⟩ hp
theorem cover_node_406 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (63/128:ℝ) with hs | hs
 · exact cover_node_402 hδ ⟨hp.1,hs⟩
 · exact cover_node_405 hδ ⟨hs,hp.2⟩
theorem cover_node_407 {δ p:ℝ} (hδ:δ∈Set.Icc (63/128:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row210 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_408 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (15/32:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (63/128:ℝ) with hs | hs
 · exact cover_node_406 ⟨hδ.1,hs⟩ hp
 · exact cover_node_407 ⟨hs,hδ.2⟩ hp
theorem cover_node_409 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (15/32:ℝ) with hs | hs
 · exact cover_node_397 hδ ⟨hp.1,hs⟩
 · exact cover_node_408 hδ ⟨hs,hp.2⟩
theorem cover_node_410 {δ p:ℝ} (hδ:δ∈Set.Icc (33/64:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row211 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_411 {δ p:ℝ} (hδ:δ∈Set.Icc (15/32:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (33/64:ℝ) with hs | hs
 · exact cover_node_409 ⟨hδ.1,hs⟩ hp
 · exact cover_node_410 ⟨hs,hδ.2⟩ hp
theorem cover_node_412 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (15/32:ℝ) with hs | hs
 · exact cover_node_396 ⟨hδ.1,hs⟩ hp
 · exact cover_node_411 ⟨hs,hδ.2⟩ hp
theorem cover_node_413 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (7/16:ℝ) with hs | hs
 · exact cover_node_355 hδ ⟨hp.1,hs⟩
 · exact cover_node_412 hδ ⟨hs,hp.2⟩
theorem cover_node_414 {δ p:ℝ} (hδ:δ∈Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact envelope_row212 (by constructor <;> linarith [hδ.1,hδ.2]) (by constructor <;> linarith [hp.1,hp.2])
theorem cover_node_415 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (1/4:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (9/16:ℝ) with hs | hs
 · exact cover_node_413 ⟨hδ.1,hs⟩ hp
 · exact cover_node_414 ⟨hs,hδ.2⟩ hp
theorem cover_node_416 {δ p:ℝ} (hδ:δ∈Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total p (1/4:ℝ) with hs | hs
 · exact cover_node_350 hδ ⟨hp.1,hs⟩
 · exact cover_node_415 hδ ⟨hs,hp.2⟩
theorem cover_node_417 {δ p:ℝ} (hδ:δ∈Set.Icc (0/1:ℝ) (3/4:ℝ))
 (hp:p∈Set.Icc (0/1:ℝ) (1/2:ℝ)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 rcases le_total δ (3/8:ℝ) with hs | hs
 · exact cover_node_349 ⟨hδ.1,hs⟩ hp
 · exact cover_node_416 ⟨hs,hδ.2⟩ hp
theorem edge_newKink_certificate {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
 (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD .newKink) (edgeC .newKink) δ p+3/4*edgeD .newKink*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 exact cover_node_417 (by simpa using hδ) (by simpa using hp)
theorem closed_envelope_return_cover (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
 (hp : p ∈ Set.Icc 0 (1/2)) : Ebase (edgeD e) (edgeC e) δ p+3/4*edgeD e*(@GenericCount.envelope countScheme kappa δ p)<theta-rowFee := by
 cases e with
 | oldSmall => exact edge_oldSmall_certificate hδ hp
 | oldPeak => exact edge_oldPeak_certificate hδ hp
 | oldSwitch => exact edge_oldSwitch_certificate hδ hp
 | newSwitch => exact edge_newSwitch_certificate hδ hp
 | newTop => exact edge_newTop_certificate hδ hp
 | newKink => exact edge_newKink_certificate hδ hp
#print axioms closed_envelope_return_cover

end
end QRH.LewkoStage1Return.IntermediateCount.Edges
