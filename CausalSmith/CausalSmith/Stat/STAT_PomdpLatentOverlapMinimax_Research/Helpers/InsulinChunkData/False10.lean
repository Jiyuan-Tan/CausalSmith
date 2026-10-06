module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part0
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part1
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part2
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part3
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part4
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part5
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part6
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part7
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part8
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part9
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part10
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part11
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part12
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part13
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part14
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part15
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part16
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part17
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part18
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part19
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part20
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part21
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part22
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part23
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part24
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part25
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part26
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part27
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part28
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part29
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part30
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part31
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part32
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part33
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part34
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10Part35

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- For [the j input](hyp:j), [this defines the insulin False Chunk Step10 object](goal). -/
def insulinFalseChunkStep10 (j : Fin 360) : InsulinChunkCoordinateData :=
  match j.val with
  | 0 => insulinFalseChunkStep10Coordinate0
  | 1 => insulinFalseChunkStep10Coordinate1
  | 2 => insulinFalseChunkStep10Coordinate2
  | 3 => insulinFalseChunkStep10Coordinate3
  | 4 => insulinFalseChunkStep10Coordinate4
  | 5 => insulinFalseChunkStep10Coordinate5
  | 6 => insulinFalseChunkStep10Coordinate6
  | 7 => insulinFalseChunkStep10Coordinate7
  | 8 => insulinFalseChunkStep10Coordinate8
  | 9 => insulinFalseChunkStep10Coordinate9
  | 10 => insulinFalseChunkStep10Coordinate10
  | 11 => insulinFalseChunkStep10Coordinate11
  | 12 => insulinFalseChunkStep10Coordinate12
  | 13 => insulinFalseChunkStep10Coordinate13
  | 14 => insulinFalseChunkStep10Coordinate14
  | 15 => insulinFalseChunkStep10Coordinate15
  | 16 => insulinFalseChunkStep10Coordinate16
  | 17 => insulinFalseChunkStep10Coordinate17
  | 18 => insulinFalseChunkStep10Coordinate18
  | 19 => insulinFalseChunkStep10Coordinate19
  | 20 => insulinFalseChunkStep10Coordinate20
  | 21 => insulinFalseChunkStep10Coordinate21
  | 22 => insulinFalseChunkStep10Coordinate22
  | 23 => insulinFalseChunkStep10Coordinate23
  | 24 => insulinFalseChunkStep10Coordinate24
  | 25 => insulinFalseChunkStep10Coordinate25
  | 26 => insulinFalseChunkStep10Coordinate26
  | 27 => insulinFalseChunkStep10Coordinate27
  | 28 => insulinFalseChunkStep10Coordinate28
  | 29 => insulinFalseChunkStep10Coordinate29
  | 30 => insulinFalseChunkStep10Coordinate30
  | 31 => insulinFalseChunkStep10Coordinate31
  | 32 => insulinFalseChunkStep10Coordinate32
  | 33 => insulinFalseChunkStep10Coordinate33
  | 34 => insulinFalseChunkStep10Coordinate34
  | 35 => insulinFalseChunkStep10Coordinate35
  | 36 => insulinFalseChunkStep10Coordinate36
  | 37 => insulinFalseChunkStep10Coordinate37
  | 38 => insulinFalseChunkStep10Coordinate38
  | 39 => insulinFalseChunkStep10Coordinate39
  | 40 => insulinFalseChunkStep10Coordinate40
  | 41 => insulinFalseChunkStep10Coordinate41
  | 42 => insulinFalseChunkStep10Coordinate42
  | 43 => insulinFalseChunkStep10Coordinate43
  | 44 => insulinFalseChunkStep10Coordinate44
  | 45 => insulinFalseChunkStep10Coordinate45
  | 46 => insulinFalseChunkStep10Coordinate46
  | 47 => insulinFalseChunkStep10Coordinate47
  | 48 => insulinFalseChunkStep10Coordinate48
  | 49 => insulinFalseChunkStep10Coordinate49
  | 50 => insulinFalseChunkStep10Coordinate50
  | 51 => insulinFalseChunkStep10Coordinate51
  | 52 => insulinFalseChunkStep10Coordinate52
  | 53 => insulinFalseChunkStep10Coordinate53
  | 54 => insulinFalseChunkStep10Coordinate54
  | 55 => insulinFalseChunkStep10Coordinate55
  | 56 => insulinFalseChunkStep10Coordinate56
  | 57 => insulinFalseChunkStep10Coordinate57
  | 58 => insulinFalseChunkStep10Coordinate58
  | 59 => insulinFalseChunkStep10Coordinate59
  | 60 => insulinFalseChunkStep10Coordinate60
  | 61 => insulinFalseChunkStep10Coordinate61
  | 62 => insulinFalseChunkStep10Coordinate62
  | 63 => insulinFalseChunkStep10Coordinate63
  | 64 => insulinFalseChunkStep10Coordinate64
  | 65 => insulinFalseChunkStep10Coordinate65
  | 66 => insulinFalseChunkStep10Coordinate66
  | 67 => insulinFalseChunkStep10Coordinate67
  | 68 => insulinFalseChunkStep10Coordinate68
  | 69 => insulinFalseChunkStep10Coordinate69
  | 70 => insulinFalseChunkStep10Coordinate70
  | 71 => insulinFalseChunkStep10Coordinate71
  | 72 => insulinFalseChunkStep10Coordinate72
  | 73 => insulinFalseChunkStep10Coordinate73
  | 74 => insulinFalseChunkStep10Coordinate74
  | 75 => insulinFalseChunkStep10Coordinate75
  | 76 => insulinFalseChunkStep10Coordinate76
  | 77 => insulinFalseChunkStep10Coordinate77
  | 78 => insulinFalseChunkStep10Coordinate78
  | 79 => insulinFalseChunkStep10Coordinate79
  | 80 => insulinFalseChunkStep10Coordinate80
  | 81 => insulinFalseChunkStep10Coordinate81
  | 82 => insulinFalseChunkStep10Coordinate82
  | 83 => insulinFalseChunkStep10Coordinate83
  | 84 => insulinFalseChunkStep10Coordinate84
  | 85 => insulinFalseChunkStep10Coordinate85
  | 86 => insulinFalseChunkStep10Coordinate86
  | 87 => insulinFalseChunkStep10Coordinate87
  | 88 => insulinFalseChunkStep10Coordinate88
  | 89 => insulinFalseChunkStep10Coordinate89
  | 90 => insulinFalseChunkStep10Coordinate90
  | 91 => insulinFalseChunkStep10Coordinate91
  | 92 => insulinFalseChunkStep10Coordinate92
  | 93 => insulinFalseChunkStep10Coordinate93
  | 94 => insulinFalseChunkStep10Coordinate94
  | 95 => insulinFalseChunkStep10Coordinate95
  | 96 => insulinFalseChunkStep10Coordinate96
  | 97 => insulinFalseChunkStep10Coordinate97
  | 98 => insulinFalseChunkStep10Coordinate98
  | 99 => insulinFalseChunkStep10Coordinate99
  | 100 => insulinFalseChunkStep10Coordinate100
  | 101 => insulinFalseChunkStep10Coordinate101
  | 102 => insulinFalseChunkStep10Coordinate102
  | 103 => insulinFalseChunkStep10Coordinate103
  | 104 => insulinFalseChunkStep10Coordinate104
  | 105 => insulinFalseChunkStep10Coordinate105
  | 106 => insulinFalseChunkStep10Coordinate106
  | 107 => insulinFalseChunkStep10Coordinate107
  | 108 => insulinFalseChunkStep10Coordinate108
  | 109 => insulinFalseChunkStep10Coordinate109
  | 110 => insulinFalseChunkStep10Coordinate110
  | 111 => insulinFalseChunkStep10Coordinate111
  | 112 => insulinFalseChunkStep10Coordinate112
  | 113 => insulinFalseChunkStep10Coordinate113
  | 114 => insulinFalseChunkStep10Coordinate114
  | 115 => insulinFalseChunkStep10Coordinate115
  | 116 => insulinFalseChunkStep10Coordinate116
  | 117 => insulinFalseChunkStep10Coordinate117
  | 118 => insulinFalseChunkStep10Coordinate118
  | 119 => insulinFalseChunkStep10Coordinate119
  | 120 => insulinFalseChunkStep10Coordinate120
  | 121 => insulinFalseChunkStep10Coordinate121
  | 122 => insulinFalseChunkStep10Coordinate122
  | 123 => insulinFalseChunkStep10Coordinate123
  | 124 => insulinFalseChunkStep10Coordinate124
  | 125 => insulinFalseChunkStep10Coordinate125
  | 126 => insulinFalseChunkStep10Coordinate126
  | 127 => insulinFalseChunkStep10Coordinate127
  | 128 => insulinFalseChunkStep10Coordinate128
  | 129 => insulinFalseChunkStep10Coordinate129
  | 130 => insulinFalseChunkStep10Coordinate130
  | 131 => insulinFalseChunkStep10Coordinate131
  | 132 => insulinFalseChunkStep10Coordinate132
  | 133 => insulinFalseChunkStep10Coordinate133
  | 134 => insulinFalseChunkStep10Coordinate134
  | 135 => insulinFalseChunkStep10Coordinate135
  | 136 => insulinFalseChunkStep10Coordinate136
  | 137 => insulinFalseChunkStep10Coordinate137
  | 138 => insulinFalseChunkStep10Coordinate138
  | 139 => insulinFalseChunkStep10Coordinate139
  | 140 => insulinFalseChunkStep10Coordinate140
  | 141 => insulinFalseChunkStep10Coordinate141
  | 142 => insulinFalseChunkStep10Coordinate142
  | 143 => insulinFalseChunkStep10Coordinate143
  | 144 => insulinFalseChunkStep10Coordinate144
  | 145 => insulinFalseChunkStep10Coordinate145
  | 146 => insulinFalseChunkStep10Coordinate146
  | 147 => insulinFalseChunkStep10Coordinate147
  | 148 => insulinFalseChunkStep10Coordinate148
  | 149 => insulinFalseChunkStep10Coordinate149
  | 150 => insulinFalseChunkStep10Coordinate150
  | 151 => insulinFalseChunkStep10Coordinate151
  | 152 => insulinFalseChunkStep10Coordinate152
  | 153 => insulinFalseChunkStep10Coordinate153
  | 154 => insulinFalseChunkStep10Coordinate154
  | 155 => insulinFalseChunkStep10Coordinate155
  | 156 => insulinFalseChunkStep10Coordinate156
  | 157 => insulinFalseChunkStep10Coordinate157
  | 158 => insulinFalseChunkStep10Coordinate158
  | 159 => insulinFalseChunkStep10Coordinate159
  | 160 => insulinFalseChunkStep10Coordinate160
  | 161 => insulinFalseChunkStep10Coordinate161
  | 162 => insulinFalseChunkStep10Coordinate162
  | 163 => insulinFalseChunkStep10Coordinate163
  | 164 => insulinFalseChunkStep10Coordinate164
  | 165 => insulinFalseChunkStep10Coordinate165
  | 166 => insulinFalseChunkStep10Coordinate166
  | 167 => insulinFalseChunkStep10Coordinate167
  | 168 => insulinFalseChunkStep10Coordinate168
  | 169 => insulinFalseChunkStep10Coordinate169
  | 170 => insulinFalseChunkStep10Coordinate170
  | 171 => insulinFalseChunkStep10Coordinate171
  | 172 => insulinFalseChunkStep10Coordinate172
  | 173 => insulinFalseChunkStep10Coordinate173
  | 174 => insulinFalseChunkStep10Coordinate174
  | 175 => insulinFalseChunkStep10Coordinate175
  | 176 => insulinFalseChunkStep10Coordinate176
  | 177 => insulinFalseChunkStep10Coordinate177
  | 178 => insulinFalseChunkStep10Coordinate178
  | 179 => insulinFalseChunkStep10Coordinate179
  | 180 => insulinFalseChunkStep10Coordinate180
  | 181 => insulinFalseChunkStep10Coordinate181
  | 182 => insulinFalseChunkStep10Coordinate182
  | 183 => insulinFalseChunkStep10Coordinate183
  | 184 => insulinFalseChunkStep10Coordinate184
  | 185 => insulinFalseChunkStep10Coordinate185
  | 186 => insulinFalseChunkStep10Coordinate186
  | 187 => insulinFalseChunkStep10Coordinate187
  | 188 => insulinFalseChunkStep10Coordinate188
  | 189 => insulinFalseChunkStep10Coordinate189
  | 190 => insulinFalseChunkStep10Coordinate190
  | 191 => insulinFalseChunkStep10Coordinate191
  | 192 => insulinFalseChunkStep10Coordinate192
  | 193 => insulinFalseChunkStep10Coordinate193
  | 194 => insulinFalseChunkStep10Coordinate194
  | 195 => insulinFalseChunkStep10Coordinate195
  | 196 => insulinFalseChunkStep10Coordinate196
  | 197 => insulinFalseChunkStep10Coordinate197
  | 198 => insulinFalseChunkStep10Coordinate198
  | 199 => insulinFalseChunkStep10Coordinate199
  | 200 => insulinFalseChunkStep10Coordinate200
  | 201 => insulinFalseChunkStep10Coordinate201
  | 202 => insulinFalseChunkStep10Coordinate202
  | 203 => insulinFalseChunkStep10Coordinate203
  | 204 => insulinFalseChunkStep10Coordinate204
  | 205 => insulinFalseChunkStep10Coordinate205
  | 206 => insulinFalseChunkStep10Coordinate206
  | 207 => insulinFalseChunkStep10Coordinate207
  | 208 => insulinFalseChunkStep10Coordinate208
  | 209 => insulinFalseChunkStep10Coordinate209
  | 210 => insulinFalseChunkStep10Coordinate210
  | 211 => insulinFalseChunkStep10Coordinate211
  | 212 => insulinFalseChunkStep10Coordinate212
  | 213 => insulinFalseChunkStep10Coordinate213
  | 214 => insulinFalseChunkStep10Coordinate214
  | 215 => insulinFalseChunkStep10Coordinate215
  | 216 => insulinFalseChunkStep10Coordinate216
  | 217 => insulinFalseChunkStep10Coordinate217
  | 218 => insulinFalseChunkStep10Coordinate218
  | 219 => insulinFalseChunkStep10Coordinate219
  | 220 => insulinFalseChunkStep10Coordinate220
  | 221 => insulinFalseChunkStep10Coordinate221
  | 222 => insulinFalseChunkStep10Coordinate222
  | 223 => insulinFalseChunkStep10Coordinate223
  | 224 => insulinFalseChunkStep10Coordinate224
  | 225 => insulinFalseChunkStep10Coordinate225
  | 226 => insulinFalseChunkStep10Coordinate226
  | 227 => insulinFalseChunkStep10Coordinate227
  | 228 => insulinFalseChunkStep10Coordinate228
  | 229 => insulinFalseChunkStep10Coordinate229
  | 230 => insulinFalseChunkStep10Coordinate230
  | 231 => insulinFalseChunkStep10Coordinate231
  | 232 => insulinFalseChunkStep10Coordinate232
  | 233 => insulinFalseChunkStep10Coordinate233
  | 234 => insulinFalseChunkStep10Coordinate234
  | 235 => insulinFalseChunkStep10Coordinate235
  | 236 => insulinFalseChunkStep10Coordinate236
  | 237 => insulinFalseChunkStep10Coordinate237
  | 238 => insulinFalseChunkStep10Coordinate238
  | 239 => insulinFalseChunkStep10Coordinate239
  | 240 => insulinFalseChunkStep10Coordinate240
  | 241 => insulinFalseChunkStep10Coordinate241
  | 242 => insulinFalseChunkStep10Coordinate242
  | 243 => insulinFalseChunkStep10Coordinate243
  | 244 => insulinFalseChunkStep10Coordinate244
  | 245 => insulinFalseChunkStep10Coordinate245
  | 246 => insulinFalseChunkStep10Coordinate246
  | 247 => insulinFalseChunkStep10Coordinate247
  | 248 => insulinFalseChunkStep10Coordinate248
  | 249 => insulinFalseChunkStep10Coordinate249
  | 250 => insulinFalseChunkStep10Coordinate250
  | 251 => insulinFalseChunkStep10Coordinate251
  | 252 => insulinFalseChunkStep10Coordinate252
  | 253 => insulinFalseChunkStep10Coordinate253
  | 254 => insulinFalseChunkStep10Coordinate254
  | 255 => insulinFalseChunkStep10Coordinate255
  | 256 => insulinFalseChunkStep10Coordinate256
  | 257 => insulinFalseChunkStep10Coordinate257
  | 258 => insulinFalseChunkStep10Coordinate258
  | 259 => insulinFalseChunkStep10Coordinate259
  | 260 => insulinFalseChunkStep10Coordinate260
  | 261 => insulinFalseChunkStep10Coordinate261
  | 262 => insulinFalseChunkStep10Coordinate262
  | 263 => insulinFalseChunkStep10Coordinate263
  | 264 => insulinFalseChunkStep10Coordinate264
  | 265 => insulinFalseChunkStep10Coordinate265
  | 266 => insulinFalseChunkStep10Coordinate266
  | 267 => insulinFalseChunkStep10Coordinate267
  | 268 => insulinFalseChunkStep10Coordinate268
  | 269 => insulinFalseChunkStep10Coordinate269
  | 270 => insulinFalseChunkStep10Coordinate270
  | 271 => insulinFalseChunkStep10Coordinate271
  | 272 => insulinFalseChunkStep10Coordinate272
  | 273 => insulinFalseChunkStep10Coordinate273
  | 274 => insulinFalseChunkStep10Coordinate274
  | 275 => insulinFalseChunkStep10Coordinate275
  | 276 => insulinFalseChunkStep10Coordinate276
  | 277 => insulinFalseChunkStep10Coordinate277
  | 278 => insulinFalseChunkStep10Coordinate278
  | 279 => insulinFalseChunkStep10Coordinate279
  | 280 => insulinFalseChunkStep10Coordinate280
  | 281 => insulinFalseChunkStep10Coordinate281
  | 282 => insulinFalseChunkStep10Coordinate282
  | 283 => insulinFalseChunkStep10Coordinate283
  | 284 => insulinFalseChunkStep10Coordinate284
  | 285 => insulinFalseChunkStep10Coordinate285
  | 286 => insulinFalseChunkStep10Coordinate286
  | 287 => insulinFalseChunkStep10Coordinate287
  | 288 => insulinFalseChunkStep10Coordinate288
  | 289 => insulinFalseChunkStep10Coordinate289
  | 290 => insulinFalseChunkStep10Coordinate290
  | 291 => insulinFalseChunkStep10Coordinate291
  | 292 => insulinFalseChunkStep10Coordinate292
  | 293 => insulinFalseChunkStep10Coordinate293
  | 294 => insulinFalseChunkStep10Coordinate294
  | 295 => insulinFalseChunkStep10Coordinate295
  | 296 => insulinFalseChunkStep10Coordinate296
  | 297 => insulinFalseChunkStep10Coordinate297
  | 298 => insulinFalseChunkStep10Coordinate298
  | 299 => insulinFalseChunkStep10Coordinate299
  | 300 => insulinFalseChunkStep10Coordinate300
  | 301 => insulinFalseChunkStep10Coordinate301
  | 302 => insulinFalseChunkStep10Coordinate302
  | 303 => insulinFalseChunkStep10Coordinate303
  | 304 => insulinFalseChunkStep10Coordinate304
  | 305 => insulinFalseChunkStep10Coordinate305
  | 306 => insulinFalseChunkStep10Coordinate306
  | 307 => insulinFalseChunkStep10Coordinate307
  | 308 => insulinFalseChunkStep10Coordinate308
  | 309 => insulinFalseChunkStep10Coordinate309
  | 310 => insulinFalseChunkStep10Coordinate310
  | 311 => insulinFalseChunkStep10Coordinate311
  | 312 => insulinFalseChunkStep10Coordinate312
  | 313 => insulinFalseChunkStep10Coordinate313
  | 314 => insulinFalseChunkStep10Coordinate314
  | 315 => insulinFalseChunkStep10Coordinate315
  | 316 => insulinFalseChunkStep10Coordinate316
  | 317 => insulinFalseChunkStep10Coordinate317
  | 318 => insulinFalseChunkStep10Coordinate318
  | 319 => insulinFalseChunkStep10Coordinate319
  | 320 => insulinFalseChunkStep10Coordinate320
  | 321 => insulinFalseChunkStep10Coordinate321
  | 322 => insulinFalseChunkStep10Coordinate322
  | 323 => insulinFalseChunkStep10Coordinate323
  | 324 => insulinFalseChunkStep10Coordinate324
  | 325 => insulinFalseChunkStep10Coordinate325
  | 326 => insulinFalseChunkStep10Coordinate326
  | 327 => insulinFalseChunkStep10Coordinate327
  | 328 => insulinFalseChunkStep10Coordinate328
  | 329 => insulinFalseChunkStep10Coordinate329
  | 330 => insulinFalseChunkStep10Coordinate330
  | 331 => insulinFalseChunkStep10Coordinate331
  | 332 => insulinFalseChunkStep10Coordinate332
  | 333 => insulinFalseChunkStep10Coordinate333
  | 334 => insulinFalseChunkStep10Coordinate334
  | 335 => insulinFalseChunkStep10Coordinate335
  | 336 => insulinFalseChunkStep10Coordinate336
  | 337 => insulinFalseChunkStep10Coordinate337
  | 338 => insulinFalseChunkStep10Coordinate338
  | 339 => insulinFalseChunkStep10Coordinate339
  | 340 => insulinFalseChunkStep10Coordinate340
  | 341 => insulinFalseChunkStep10Coordinate341
  | 342 => insulinFalseChunkStep10Coordinate342
  | 343 => insulinFalseChunkStep10Coordinate343
  | 344 => insulinFalseChunkStep10Coordinate344
  | 345 => insulinFalseChunkStep10Coordinate345
  | 346 => insulinFalseChunkStep10Coordinate346
  | 347 => insulinFalseChunkStep10Coordinate347
  | 348 => insulinFalseChunkStep10Coordinate348
  | 349 => insulinFalseChunkStep10Coordinate349
  | 350 => insulinFalseChunkStep10Coordinate350
  | 351 => insulinFalseChunkStep10Coordinate351
  | 352 => insulinFalseChunkStep10Coordinate352
  | 353 => insulinFalseChunkStep10Coordinate353
  | 354 => insulinFalseChunkStep10Coordinate354
  | 355 => insulinFalseChunkStep10Coordinate355
  | 356 => insulinFalseChunkStep10Coordinate356
  | 357 => insulinFalseChunkStep10Coordinate357
  | 358 => insulinFalseChunkStep10Coordinate358
  | _ => insulinFalseChunkStep10Coordinate359

end CausalSmith.Stat.PomdpLatentOverlapMinimax
