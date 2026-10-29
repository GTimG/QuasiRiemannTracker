/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.CountWindow
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission01
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission02
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission03
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission04
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission05
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission06
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission07
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission08
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission09
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission10
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission11
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission12
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission13
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission14
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission15
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission16
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission17
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission18
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission19
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission20
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission21
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission22
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission23
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission24
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission25
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission26
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission27
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission28
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission29
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission30
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission31
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission32
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission33
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission34
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission35
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission36
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission37
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission38
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission39
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission40
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission41
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission42
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission43
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission44
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission45
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission46
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission47
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission48
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission49
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission50
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission51
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission52
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission53
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission54
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission55
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission56
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission57
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission58
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission59
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission60
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission61
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission62
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission63
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission64
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission65
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission66
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission67
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission68
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission69
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission70
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission71
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission72
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission73
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission74
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission75
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission76
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission77
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission78
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission79
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission80
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission81
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission82
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission83
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission84
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission85
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission86
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission87
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission88
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission89
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission90
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission91
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission92
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission93
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission94
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission95
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission96
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission97
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission98
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission99
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission100
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission101
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission102
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission103
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission104
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission105
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission106
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission107
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission108
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission109
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission110
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission111
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission112
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission113
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission114
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission115
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission116
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission117
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission118
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission119
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission120
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission121
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission122
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission123
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission124
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission125
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission126
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission127
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission128
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission129
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission130
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission131
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission132
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission133
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission134
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission135
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission136
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission137
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission138
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission139
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission140
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission141
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission142
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission143
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission144
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission145
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission146
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission147
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission148
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission149
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission150
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission151
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission152
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission153
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission154
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission155
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission156
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission157
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission158
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission159
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission160
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission161
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission162
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission163
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission164
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission165
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission166
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission167
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission168
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission169
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission170
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission171
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission172
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission173
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission174
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission175
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission176
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission177
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission178
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission179
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission180
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission181
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission182
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission183
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission184
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission185
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission186
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission187
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission188
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission189
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission190
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission191
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission192
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission193
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission194
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission195
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission196
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission197
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission198
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission199
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission200
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission201
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission202
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission203
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission204
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission205
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission206
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission207
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission208
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission209
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission210
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission211
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission212
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission213
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission214
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission215
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission216
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission217
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission218
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission219
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission220
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission221
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission222
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission223
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission224
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission225
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission226
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission227
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission228
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission229
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission230
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission231
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission232
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission233
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission234
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission235
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission236
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission237
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission238
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission239
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission240
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission241
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission242
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission243
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission244
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission245
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission246
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission247
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission248
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission249
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission250
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission251
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission252
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission253
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission254
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission255
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission256
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission257
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission258
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission259
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission260
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission261
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission262
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission263
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission264
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission265
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission266
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission267
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission268
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission269
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission270
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission271
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission272
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission273
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission274
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission275
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission276
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission277
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission278
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission279
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission280
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission281
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission282
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Rows.Admission283
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.RayCurveReturn
open QRH.Record1252270103Return
noncomputable section

def returnWindow01 : ReturnCountWindow where
 branch := .Pnew
 nonold := by decide
 deltaLo := (9/32:ℝ)
 deltaHi := (3/8:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission01_all

def returnWindow02 : ReturnCountWindow where
 branch := .Pnew
 nonold := by decide
 deltaLo := (9/32:ℝ)
 deltaHi := (21/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission02_all

def returnWindow03 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission03_all

def returnWindow04 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (225/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission04_all

def returnWindow05 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission05_all

def returnWindow06 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (453/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission06_all

def returnWindow07 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (453/1024:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission07_all

def returnWindow08 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission08_all

def returnWindow09 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission09_all

def returnWindow10 : ReturnCountWindow where
 branch := .Pnew
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission10_all

def returnWindow11 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission11_all

def returnWindow12 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission12_all

def returnWindow13 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission13_all

def returnWindow14 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission14_all

def returnWindow15 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (111/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission15_all

def returnWindow16 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission16_all

def returnWindow17 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (225/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission17_all

def returnWindow18 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission18_all

def returnWindow19 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (453/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission19_all

def returnWindow20 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (453/1024:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission20_all

def returnWindow21 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission21_all

def returnWindow22 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission22_all

def returnWindow23 : ReturnCountWindow where
 branch := .Pold
 nonold := by decide
 deltaLo := (9/32:ℝ)
 deltaHi := (3/8:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission23_all

def returnWindow24 : ReturnCountWindow where
 branch := .Pold
 nonold := by decide
 deltaLo := (9/32:ℝ)
 deltaHi := (21/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission24_all

def returnWindow25 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission25_all

def returnWindow26 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission26_all

def returnWindow27 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission27_all

def returnWindow28 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission28_all

def returnWindow29 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (111/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission29_all

def returnWindow30 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission30_all

def returnWindow31 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (225/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission31_all

def returnWindow32 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission32_all

def returnWindow33 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (453/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission33_all

def returnWindow34 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (453/1024:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission34_all

def returnWindow35 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission35_all

def returnWindow36 : ReturnCountWindow where
 branch := .Cold
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission36_all

def returnWindow37 : ReturnCountWindow where
 branch := .Pold
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission37_all

def returnWindow38 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (21/64:ℝ)
 deltaHi := (3/8:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission38_all

def returnWindow39 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission39_all

def returnWindow40 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission40_all

def returnWindow41 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission41_all

def returnWindow42 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission42_all

def returnWindow43 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (111/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission43_all

def returnWindow44 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission44_all

def returnWindow45 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (225/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission45_all

def returnWindow46 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission46_all

def returnWindow47 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (453/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission47_all

def returnWindow48 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (453/1024:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission48_all

def returnWindow49 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission49_all

def returnWindow50 : ReturnCountWindow where
 branch := .Cphysold
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission50_all

def returnWindow51 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (215/512:ℝ)
 deltaHi := (431/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission51_all

def returnWindow52 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (431/1024:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission52_all

def returnWindow53 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (55/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission53_all

def returnWindow54 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (55/128:ℝ)
 deltaHi := (7/16:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission54_all

def returnWindow55 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (7/16:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission55_all

def returnWindow56 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (29/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission56_all

def returnWindow57 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (29/64:ℝ)
 deltaHi := (59/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission57_all

def returnWindow58 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (59/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission58_all

def returnWindow59 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (61/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission59_all

def returnWindow60 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (61/128:ℝ)
 deltaHi := (31/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission60_all

def returnWindow61 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (31/64:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission61_all

def returnWindow62 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (1/2:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission62_all

def returnWindow63 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (1/2:ℝ)
 deltaHi := (65/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission63_all

def returnWindow64 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (65/128:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission64_all

def returnWindow65 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (67/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission65_all

def returnWindow66 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (67/128:ℝ)
 deltaHi := (17/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission66_all

def returnWindow67 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (17/32:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission67_all

def returnWindow68 : ReturnCountWindow where
 branch := .Cnew
 nonold := by decide
 deltaLo := (69/128:ℝ)
 deltaHi := (35/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission68_all

def returnWindow69 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (61/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission69_all

def returnWindow70 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (61/128:ℝ)
 deltaHi := (31/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission70_all

def returnWindow71 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (31/64:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission71_all

def returnWindow72 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (1/2:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission72_all

def returnWindow73 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (1/2:ℝ)
 deltaHi := (65/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission73_all

def returnWindow74 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (65/128:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission74_all

def returnWindow75 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (67/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission75_all

def returnWindow76 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (67/128:ℝ)
 deltaHi := (17/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission76_all

def returnWindow77 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (17/32:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission77_all

def returnWindow78 : ReturnCountWindow where
 branch := .Cphys
 nonold := by decide
 deltaLo := (69/128:ℝ)
 deltaHi := (35/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission78_all

def returnWindow79 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (5/16:ℝ)
 deltaHi := (41/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission79_all

def returnWindow80 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (41/128:ℝ)
 deltaHi := (21/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission80_all

def returnWindow81 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (21/64:ℝ)
 deltaHi := (43/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission81_all

def returnWindow82 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (43/128:ℝ)
 deltaHi := (11/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission82_all

def returnWindow83 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (11/32:ℝ)
 deltaHi := (45/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission83_all

def returnWindow84 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (45/128:ℝ)
 deltaHi := (23/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission84_all

def returnWindow85 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (23/64:ℝ)
 deltaHi := (47/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission85_all

def returnWindow86 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (47/128:ℝ)
 deltaHi := (3/8:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission86_all

def returnWindow87 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (49/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission87_all

def returnWindow88 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (49/128:ℝ)
 deltaHi := (25/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission88_all

def returnWindow89 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (25/64:ℝ)
 deltaHi := (51/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission89_all

def returnWindow90 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (51/128:ℝ)
 deltaHi := (13/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission90_all

def returnWindow91 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (13/32:ℝ)
 deltaHi := (53/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission91_all

def returnWindow92 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (53/128:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission92_all

def returnWindow93 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (55/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission93_all

def returnWindow94 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (55/128:ℝ)
 deltaHi := (7/16:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission94_all

def returnWindow95 : ReturnCountWindow where
 branch := .Pwide
 nonold := by decide
 deltaLo := (7/16:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission95_all

def returnWindow96 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (49/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission96_all

def returnWindow97 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (49/128:ℝ)
 deltaHi := (25/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission97_all

def returnWindow98 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (25/64:ℝ)
 deltaHi := (51/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission98_all

def returnWindow99 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (51/128:ℝ)
 deltaHi := (13/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission99_all

def returnWindow100 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (13/32:ℝ)
 deltaHi := (53/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission100_all

def returnWindow101 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (53/128:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission101_all

def returnWindow102 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (55/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission102_all

def returnWindow103 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (55/128:ℝ)
 deltaHi := (7/16:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission103_all

def returnWindow104 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (7/16:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission104_all

def returnWindow105 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (29/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission105_all

def returnWindow106 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (29/64:ℝ)
 deltaHi := (59/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission106_all

def returnWindow107 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (59/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission107_all

def returnWindow108 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (61/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission108_all

def returnWindow109 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (61/128:ℝ)
 deltaHi := (31/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission109_all

def returnWindow110 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (31/64:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission110_all

def returnWindow111 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (1/2:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission111_all

def returnWindow112 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (1/2:ℝ)
 deltaHi := (65/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission112_all

def returnWindow113 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (65/128:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission113_all

def returnWindow114 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (67/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission114_all

def returnWindow115 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (67/128:ℝ)
 deltaHi := (17/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission115_all

def returnWindow116 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (17/32:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission116_all

def returnWindow117 : ReturnCountWindow where
 branch := .Cbridge0
 nonold := by decide
 deltaLo := (69/128:ℝ)
 deltaHi := (35/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission117_all

def returnWindow118 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (401/1024:ℝ)
 deltaHi := (201/512:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission118_all

def returnWindow119 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (201/512:ℝ)
 deltaHi := (403/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission119_all

def returnWindow120 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (403/1024:ℝ)
 deltaHi := (101/256:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission120_all

def returnWindow121 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (101/256:ℝ)
 deltaHi := (405/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission121_all

def returnWindow122 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (405/1024:ℝ)
 deltaHi := (203/512:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission122_all

def returnWindow123 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (203/512:ℝ)
 deltaHi := (407/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission123_all

def returnWindow124 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (407/1024:ℝ)
 deltaHi := (51/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission124_all

def returnWindow125 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (51/128:ℝ)
 deltaHi := (13/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission125_all

def returnWindow126 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (13/32:ℝ)
 deltaHi := (53/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission126_all

def returnWindow127 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (53/128:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission127_all

def returnWindow128 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (55/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission128_all

def returnWindow129 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (55/128:ℝ)
 deltaHi := (7/16:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission129_all

def returnWindow130 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (7/16:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission130_all

def returnWindow131 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (29/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission131_all

def returnWindow132 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (29/64:ℝ)
 deltaHi := (59/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission132_all

def returnWindow133 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (59/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission133_all

def returnWindow134 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (61/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission134_all

def returnWindow135 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (61/128:ℝ)
 deltaHi := (31/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission135_all

def returnWindow136 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (31/64:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission136_all

def returnWindow137 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (1/2:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission137_all

def returnWindow138 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (1/2:ℝ)
 deltaHi := (65/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission138_all

def returnWindow139 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (65/128:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission139_all

def returnWindow140 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (67/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission140_all

def returnWindow141 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (67/128:ℝ)
 deltaHi := (17/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission141_all

def returnWindow142 : ReturnCountWindow where
 branch := .Cbridge1
 nonold := by decide
 deltaLo := (17/32:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission142_all

def returnWindow143 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (417/1024:ℝ)
 deltaHi := (209/512:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission143_all

def returnWindow144 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (209/512:ℝ)
 deltaHi := (419/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission144_all

def returnWindow145 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (419/1024:ℝ)
 deltaHi := (105/256:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission145_all

def returnWindow146 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (105/256:ℝ)
 deltaHi := (421/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission146_all

def returnWindow147 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (421/1024:ℝ)
 deltaHi := (211/512:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission147_all

def returnWindow148 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (211/512:ℝ)
 deltaHi := (423/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission148_all

def returnWindow149 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (423/1024:ℝ)
 deltaHi := (53/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission149_all

def returnWindow150 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (53/128:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission150_all

def returnWindow151 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (55/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission151_all

def returnWindow152 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (55/128:ℝ)
 deltaHi := (7/16:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission152_all

def returnWindow153 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (7/16:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission153_all

def returnWindow154 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (29/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission154_all

def returnWindow155 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (29/64:ℝ)
 deltaHi := (59/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission155_all

def returnWindow156 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (59/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission156_all

def returnWindow157 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (61/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission157_all

def returnWindow158 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (61/128:ℝ)
 deltaHi := (31/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission158_all

def returnWindow159 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (31/64:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission159_all

def returnWindow160 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (1/2:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission160_all

def returnWindow161 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (1/2:ℝ)
 deltaHi := (65/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission161_all

def returnWindow162 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (65/128:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission162_all

def returnWindow163 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (67/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission163_all

def returnWindow164 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (67/128:ℝ)
 deltaHi := (17/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission164_all

def returnWindow165 : ReturnCountWindow where
 branch := .Cbridge2
 nonold := by decide
 deltaLo := (17/32:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission165_all

def returnWindow166 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (427/1024:ℝ)
 deltaHi := (107/256:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission166_all

def returnWindow167 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (107/256:ℝ)
 deltaHi := (429/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission167_all

def returnWindow168 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (429/1024:ℝ)
 deltaHi := (215/512:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission168_all

def returnWindow169 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (215/512:ℝ)
 deltaHi := (431/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission169_all

def returnWindow170 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (431/1024:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission170_all

def returnWindow171 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (55/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission171_all

def returnWindow172 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (55/128:ℝ)
 deltaHi := (7/16:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission172_all

def returnWindow173 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (7/16:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission173_all

def returnWindow174 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (29/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission174_all

def returnWindow175 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (29/64:ℝ)
 deltaHi := (59/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission175_all

def returnWindow176 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (59/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission176_all

def returnWindow177 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (61/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission177_all

def returnWindow178 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (61/128:ℝ)
 deltaHi := (31/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission178_all

def returnWindow179 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (31/64:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission179_all

def returnWindow180 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (1/2:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission180_all

def returnWindow181 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (1/2:ℝ)
 deltaHi := (65/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission181_all

def returnWindow182 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (65/128:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission182_all

def returnWindow183 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (67/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission183_all

def returnWindow184 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (67/128:ℝ)
 deltaHi := (17/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission184_all

def returnWindow185 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (17/32:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission185_all

def returnWindow186 : ReturnCountWindow where
 branch := .Cbridge3
 nonold := by decide
 deltaLo := (69/128:ℝ)
 deltaHi := (35/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission186_all

def returnWindow187 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (433/1024:ℝ)
 deltaHi := (217/512:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission187_all

def returnWindow188 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (217/512:ℝ)
 deltaHi := (435/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission188_all

def returnWindow189 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (435/1024:ℝ)
 deltaHi := (109/256:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission189_all

def returnWindow190 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (109/256:ℝ)
 deltaHi := (437/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission190_all

def returnWindow191 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (437/1024:ℝ)
 deltaHi := (219/512:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission191_all

def returnWindow192 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (219/512:ℝ)
 deltaHi := (439/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission192_all

def returnWindow193 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (439/1024:ℝ)
 deltaHi := (55/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission193_all

def returnWindow194 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (55/128:ℝ)
 deltaHi := (7/16:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission194_all

def returnWindow195 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (7/16:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission195_all

def returnWindow196 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (29/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission196_all

def returnWindow197 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (29/64:ℝ)
 deltaHi := (59/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission197_all

def returnWindow198 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (59/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission198_all

def returnWindow199 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (61/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission199_all

def returnWindow200 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (61/128:ℝ)
 deltaHi := (31/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission200_all

def returnWindow201 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (31/64:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission201_all

def returnWindow202 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (1/2:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission202_all

def returnWindow203 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (1/2:ℝ)
 deltaHi := (65/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission203_all

def returnWindow204 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (65/128:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission204_all

def returnWindow205 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (67/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission205_all

def returnWindow206 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (67/128:ℝ)
 deltaHi := (17/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission206_all

def returnWindow207 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (17/32:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission207_all

def returnWindow208 : ReturnCountWindow where
 branch := .Cbridge4
 nonold := by decide
 deltaLo := (69/128:ℝ)
 deltaHi := (35/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission208_all

def returnWindow209 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (215/512:ℝ)
 deltaHi := (431/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission209_all

def returnWindow210 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (431/1024:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission210_all

def returnWindow211 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (55/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission211_all

def returnWindow212 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (55/128:ℝ)
 deltaHi := (7/16:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission212_all

def returnWindow213 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (7/16:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission213_all

def returnWindow214 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (29/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission214_all

def returnWindow215 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (29/64:ℝ)
 deltaHi := (59/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission215_all

def returnWindow216 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (59/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission216_all

def returnWindow217 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (61/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission217_all

def returnWindow218 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (61/128:ℝ)
 deltaHi := (31/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission218_all

def returnWindow219 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (31/64:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission219_all

def returnWindow220 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (1/2:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission220_all

def returnWindow221 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (1/2:ℝ)
 deltaHi := (65/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission221_all

def returnWindow222 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (65/128:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission222_all

def returnWindow223 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (67/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission223_all

def returnWindow224 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (67/128:ℝ)
 deltaHi := (17/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission224_all

def returnWindow225 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (17/32:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission225_all

def returnWindow226 : ReturnCountWindow where
 branch := .Cbridge5
 nonold := by decide
 deltaLo := (69/128:ℝ)
 deltaHi := (35/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission226_all

def returnWindow227 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (435/1024:ℝ)
 deltaHi := (109/256:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission227_all

def returnWindow228 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (109/256:ℝ)
 deltaHi := (437/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission228_all

def returnWindow229 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (437/1024:ℝ)
 deltaHi := (219/512:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission229_all

def returnWindow230 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (219/512:ℝ)
 deltaHi := (439/1024:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission230_all

def returnWindow231 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (439/1024:ℝ)
 deltaHi := (55/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission231_all

def returnWindow232 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (55/128:ℝ)
 deltaHi := (7/16:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission232_all

def returnWindow233 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (7/16:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission233_all

def returnWindow234 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (29/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission234_all

def returnWindow235 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (29/64:ℝ)
 deltaHi := (59/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission235_all

def returnWindow236 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (59/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission236_all

def returnWindow237 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (61/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission237_all

def returnWindow238 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (61/128:ℝ)
 deltaHi := (31/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission238_all

def returnWindow239 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (31/64:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission239_all

def returnWindow240 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (1/2:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission240_all

def returnWindow241 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (1/2:ℝ)
 deltaHi := (65/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission241_all

def returnWindow242 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (65/128:ℝ)
 deltaHi := (33/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission242_all

def returnWindow243 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (33/64:ℝ)
 deltaHi := (67/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission243_all

def returnWindow244 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (67/128:ℝ)
 deltaHi := (17/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission244_all

def returnWindow245 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (17/32:ℝ)
 deltaHi := (69/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission245_all

def returnWindow246 : ReturnCountWindow where
 branch := .Cbridge6
 nonold := by decide
 deltaLo := (69/128:ℝ)
 deltaHi := (35/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission246_all

def returnWindow247 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (41/128:ℝ)
 deltaHi := (21/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission247_all

def returnWindow248 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (21/64:ℝ)
 deltaHi := (43/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission248_all

def returnWindow249 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (43/128:ℝ)
 deltaHi := (11/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission249_all

def returnWindow250 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (11/32:ℝ)
 deltaHi := (45/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission250_all

def returnWindow251 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (45/128:ℝ)
 deltaHi := (23/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission251_all

def returnWindow252 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (23/64:ℝ)
 deltaHi := (47/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission252_all

def returnWindow253 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (47/128:ℝ)
 deltaHi := (3/8:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission253_all

def returnWindow254 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (49/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission254_all

def returnWindow255 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (49/128:ℝ)
 deltaHi := (25/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission255_all

def returnWindow256 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (25/64:ℝ)
 deltaHi := (51/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission256_all

def returnWindow257 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (51/128:ℝ)
 deltaHi := (13/32:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission257_all

def returnWindow258 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (13/32:ℝ)
 deltaHi := (53/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission258_all

def returnWindow259 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (53/128:ℝ)
 deltaHi := (425/1024:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission259_all

def returnWindow260 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (425/1024:ℝ)
 deltaHi := (213/512:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission260_all

def returnWindow261 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (213/512:ℝ)
 deltaHi := (427/1024:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission261_all

def returnWindow262 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (427/1024:ℝ)
 deltaHi := (107/256:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission262_all

def returnWindow263 : ReturnCountWindow where
 branch := .Pcount
 nonold := by decide
 deltaLo := (107/256:ℝ)
 deltaHi := (429/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission263_all

def returnWindow264 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (5/16:ℝ)
 deltaHi := (41/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission264_all

def returnWindow265 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (41/128:ℝ)
 deltaHi := (21/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission265_all

def returnWindow266 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (21/64:ℝ)
 deltaHi := (43/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission266_all

def returnWindow267 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (43/128:ℝ)
 deltaHi := (11/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission267_all

def returnWindow268 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (11/32:ℝ)
 deltaHi := (45/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission268_all

def returnWindow269 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (45/128:ℝ)
 deltaHi := (23/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission269_all

def returnWindow270 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (23/64:ℝ)
 deltaHi := (47/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission270_all

def returnWindow271 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (47/128:ℝ)
 deltaHi := (3/8:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission271_all

def returnWindow272 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (49/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission272_all

def returnWindow273 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (49/128:ℝ)
 deltaHi := (25/64:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission273_all

def returnWindow274 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (25/64:ℝ)
 deltaHi := (51/128:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission274_all

def returnWindow275 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (51/128:ℝ)
 deltaHi := (13/32:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission275_all

def returnWindow276 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (13/32:ℝ)
 deltaHi := (53/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission276_all

def returnWindow277 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (53/128:ℝ)
 deltaHi := (425/1024:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission277_all

def returnWindow278 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (425/1024:ℝ)
 deltaHi := (213/512:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission278_all

def returnWindow279 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (213/512:ℝ)
 deltaHi := (427/1024:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission279_all

def returnWindow280 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (427/1024:ℝ)
 deltaHi := (107/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission280_all

def returnWindow281 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (107/256:ℝ)
 deltaHi := (429/1024:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission281_all

def returnWindow282 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (429/1024:ℝ)
 deltaHi := (215/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission282_all

def returnWindow283 : ReturnCountWindow where
 branch := .Pcountmid
 nonold := by decide
 deltaLo := (215/512:ℝ)
 deltaHi := (431/1024:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission283_all
def returnWindows : List ReturnCountWindow := [returnWindow01,returnWindow02,returnWindow03,returnWindow04,returnWindow05,returnWindow06,returnWindow07,returnWindow08,returnWindow09,returnWindow10,returnWindow11,returnWindow12,returnWindow13,returnWindow14,returnWindow15,returnWindow16,returnWindow17,returnWindow18,returnWindow19,returnWindow20,returnWindow21,returnWindow22,returnWindow23,returnWindow24,returnWindow25,returnWindow26,returnWindow27,returnWindow28,returnWindow29,returnWindow30,returnWindow31,returnWindow32,returnWindow33,returnWindow34,returnWindow35,returnWindow36,returnWindow37,returnWindow38,returnWindow39,returnWindow40,returnWindow41,returnWindow42,returnWindow43,returnWindow44,returnWindow45,returnWindow46,returnWindow47,returnWindow48,returnWindow49,returnWindow50,returnWindow51,returnWindow52,returnWindow53,returnWindow54,returnWindow55,returnWindow56,returnWindow57,returnWindow58,returnWindow59,returnWindow60,returnWindow61,returnWindow62,returnWindow63,returnWindow64,returnWindow65,returnWindow66,returnWindow67,returnWindow68,returnWindow69,returnWindow70,returnWindow71,returnWindow72,returnWindow73,returnWindow74,returnWindow75,returnWindow76,returnWindow77,returnWindow78,returnWindow79,returnWindow80,returnWindow81,returnWindow82,returnWindow83,returnWindow84,returnWindow85,returnWindow86,returnWindow87,returnWindow88,returnWindow89,returnWindow90,returnWindow91,returnWindow92,returnWindow93,returnWindow94,returnWindow95,returnWindow96,returnWindow97,returnWindow98,returnWindow99,returnWindow100,returnWindow101,returnWindow102,returnWindow103,returnWindow104,returnWindow105,returnWindow106,returnWindow107,returnWindow108,returnWindow109,returnWindow110,returnWindow111,returnWindow112,returnWindow113,returnWindow114,returnWindow115,returnWindow116,returnWindow117,returnWindow118,returnWindow119,returnWindow120,returnWindow121,returnWindow122,returnWindow123,returnWindow124,returnWindow125,returnWindow126,returnWindow127,returnWindow128,returnWindow129,returnWindow130,returnWindow131,returnWindow132,returnWindow133,returnWindow134,returnWindow135,returnWindow136,returnWindow137,returnWindow138,returnWindow139,returnWindow140,returnWindow141,returnWindow142,returnWindow143,returnWindow144,returnWindow145,returnWindow146,returnWindow147,returnWindow148,returnWindow149,returnWindow150,returnWindow151,returnWindow152,returnWindow153,returnWindow154,returnWindow155,returnWindow156,returnWindow157,returnWindow158,returnWindow159,returnWindow160,returnWindow161,returnWindow162,returnWindow163,returnWindow164,returnWindow165,returnWindow166,returnWindow167,returnWindow168,returnWindow169,returnWindow170,returnWindow171,returnWindow172,returnWindow173,returnWindow174,returnWindow175,returnWindow176,returnWindow177,returnWindow178,returnWindow179,returnWindow180,returnWindow181,returnWindow182,returnWindow183,returnWindow184,returnWindow185,returnWindow186,returnWindow187,returnWindow188,returnWindow189,returnWindow190,returnWindow191,returnWindow192,returnWindow193,returnWindow194,returnWindow195,returnWindow196,returnWindow197,returnWindow198,returnWindow199,returnWindow200,returnWindow201,returnWindow202,returnWindow203,returnWindow204,returnWindow205,returnWindow206,returnWindow207,returnWindow208,returnWindow209,returnWindow210,returnWindow211,returnWindow212,returnWindow213,returnWindow214,returnWindow215,returnWindow216,returnWindow217,returnWindow218,returnWindow219,returnWindow220,returnWindow221,returnWindow222,returnWindow223,returnWindow224,returnWindow225,returnWindow226,returnWindow227,returnWindow228,returnWindow229,returnWindow230,returnWindow231,returnWindow232,returnWindow233,returnWindow234,returnWindow235,returnWindow236,returnWindow237,returnWindow238,returnWindow239,returnWindow240,returnWindow241,returnWindow242,returnWindow243,returnWindow244,returnWindow245,returnWindow246,returnWindow247,returnWindow248,returnWindow249,returnWindow250,returnWindow251,returnWindow252,returnWindow253,returnWindow254,returnWindow255,returnWindow256,returnWindow257,returnWindow258,returnWindow259,returnWindow260,returnWindow261,returnWindow262,returnWindow263,returnWindow264,returnWindow265,returnWindow266,returnWindow267,returnWindow268,returnWindow269,returnWindow270,returnWindow271,returnWindow272,returnWindow273,returnWindow274,returnWindow275,returnWindow276,returnWindow277,returnWindow278,returnWindow279,returnWindow280,returnWindow281,returnWindow282,returnWindow283]

end
end Qrh.JointDetector.RayCurveReturn
