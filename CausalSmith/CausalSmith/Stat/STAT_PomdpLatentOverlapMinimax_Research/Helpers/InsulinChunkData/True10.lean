module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part0
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part1
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part2
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part3
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part4
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part5
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part6
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part7
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part8
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part9
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part10
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part11
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part12
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part13
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part14
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part15
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part16
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part17
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part18
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part19
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part20
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part21
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part22
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part23
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part24
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part25
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part26
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part27
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part28
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part29
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part30
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part31
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part32
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part33
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part34
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10Part35

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- For [the j input](hyp:j), [this defines the insulin True Chunk Step10 object](goal). -/
def insulinTrueChunkStep10 (j : Fin 360) : InsulinChunkCoordinateData :=
  match j.val with
  | 0 => insulinTrueChunkStep10Coordinate0
  | 1 => insulinTrueChunkStep10Coordinate1
  | 2 => insulinTrueChunkStep10Coordinate2
  | 3 => insulinTrueChunkStep10Coordinate3
  | 4 => insulinTrueChunkStep10Coordinate4
  | 5 => insulinTrueChunkStep10Coordinate5
  | 6 => insulinTrueChunkStep10Coordinate6
  | 7 => insulinTrueChunkStep10Coordinate7
  | 8 => insulinTrueChunkStep10Coordinate8
  | 9 => insulinTrueChunkStep10Coordinate9
  | 10 => insulinTrueChunkStep10Coordinate10
  | 11 => insulinTrueChunkStep10Coordinate11
  | 12 => insulinTrueChunkStep10Coordinate12
  | 13 => insulinTrueChunkStep10Coordinate13
  | 14 => insulinTrueChunkStep10Coordinate14
  | 15 => insulinTrueChunkStep10Coordinate15
  | 16 => insulinTrueChunkStep10Coordinate16
  | 17 => insulinTrueChunkStep10Coordinate17
  | 18 => insulinTrueChunkStep10Coordinate18
  | 19 => insulinTrueChunkStep10Coordinate19
  | 20 => insulinTrueChunkStep10Coordinate20
  | 21 => insulinTrueChunkStep10Coordinate21
  | 22 => insulinTrueChunkStep10Coordinate22
  | 23 => insulinTrueChunkStep10Coordinate23
  | 24 => insulinTrueChunkStep10Coordinate24
  | 25 => insulinTrueChunkStep10Coordinate25
  | 26 => insulinTrueChunkStep10Coordinate26
  | 27 => insulinTrueChunkStep10Coordinate27
  | 28 => insulinTrueChunkStep10Coordinate28
  | 29 => insulinTrueChunkStep10Coordinate29
  | 30 => insulinTrueChunkStep10Coordinate30
  | 31 => insulinTrueChunkStep10Coordinate31
  | 32 => insulinTrueChunkStep10Coordinate32
  | 33 => insulinTrueChunkStep10Coordinate33
  | 34 => insulinTrueChunkStep10Coordinate34
  | 35 => insulinTrueChunkStep10Coordinate35
  | 36 => insulinTrueChunkStep10Coordinate36
  | 37 => insulinTrueChunkStep10Coordinate37
  | 38 => insulinTrueChunkStep10Coordinate38
  | 39 => insulinTrueChunkStep10Coordinate39
  | 40 => insulinTrueChunkStep10Coordinate40
  | 41 => insulinTrueChunkStep10Coordinate41
  | 42 => insulinTrueChunkStep10Coordinate42
  | 43 => insulinTrueChunkStep10Coordinate43
  | 44 => insulinTrueChunkStep10Coordinate44
  | 45 => insulinTrueChunkStep10Coordinate45
  | 46 => insulinTrueChunkStep10Coordinate46
  | 47 => insulinTrueChunkStep10Coordinate47
  | 48 => insulinTrueChunkStep10Coordinate48
  | 49 => insulinTrueChunkStep10Coordinate49
  | 50 => insulinTrueChunkStep10Coordinate50
  | 51 => insulinTrueChunkStep10Coordinate51
  | 52 => insulinTrueChunkStep10Coordinate52
  | 53 => insulinTrueChunkStep10Coordinate53
  | 54 => insulinTrueChunkStep10Coordinate54
  | 55 => insulinTrueChunkStep10Coordinate55
  | 56 => insulinTrueChunkStep10Coordinate56
  | 57 => insulinTrueChunkStep10Coordinate57
  | 58 => insulinTrueChunkStep10Coordinate58
  | 59 => insulinTrueChunkStep10Coordinate59
  | 60 => insulinTrueChunkStep10Coordinate60
  | 61 => insulinTrueChunkStep10Coordinate61
  | 62 => insulinTrueChunkStep10Coordinate62
  | 63 => insulinTrueChunkStep10Coordinate63
  | 64 => insulinTrueChunkStep10Coordinate64
  | 65 => insulinTrueChunkStep10Coordinate65
  | 66 => insulinTrueChunkStep10Coordinate66
  | 67 => insulinTrueChunkStep10Coordinate67
  | 68 => insulinTrueChunkStep10Coordinate68
  | 69 => insulinTrueChunkStep10Coordinate69
  | 70 => insulinTrueChunkStep10Coordinate70
  | 71 => insulinTrueChunkStep10Coordinate71
  | 72 => insulinTrueChunkStep10Coordinate72
  | 73 => insulinTrueChunkStep10Coordinate73
  | 74 => insulinTrueChunkStep10Coordinate74
  | 75 => insulinTrueChunkStep10Coordinate75
  | 76 => insulinTrueChunkStep10Coordinate76
  | 77 => insulinTrueChunkStep10Coordinate77
  | 78 => insulinTrueChunkStep10Coordinate78
  | 79 => insulinTrueChunkStep10Coordinate79
  | 80 => insulinTrueChunkStep10Coordinate80
  | 81 => insulinTrueChunkStep10Coordinate81
  | 82 => insulinTrueChunkStep10Coordinate82
  | 83 => insulinTrueChunkStep10Coordinate83
  | 84 => insulinTrueChunkStep10Coordinate84
  | 85 => insulinTrueChunkStep10Coordinate85
  | 86 => insulinTrueChunkStep10Coordinate86
  | 87 => insulinTrueChunkStep10Coordinate87
  | 88 => insulinTrueChunkStep10Coordinate88
  | 89 => insulinTrueChunkStep10Coordinate89
  | 90 => insulinTrueChunkStep10Coordinate90
  | 91 => insulinTrueChunkStep10Coordinate91
  | 92 => insulinTrueChunkStep10Coordinate92
  | 93 => insulinTrueChunkStep10Coordinate93
  | 94 => insulinTrueChunkStep10Coordinate94
  | 95 => insulinTrueChunkStep10Coordinate95
  | 96 => insulinTrueChunkStep10Coordinate96
  | 97 => insulinTrueChunkStep10Coordinate97
  | 98 => insulinTrueChunkStep10Coordinate98
  | 99 => insulinTrueChunkStep10Coordinate99
  | 100 => insulinTrueChunkStep10Coordinate100
  | 101 => insulinTrueChunkStep10Coordinate101
  | 102 => insulinTrueChunkStep10Coordinate102
  | 103 => insulinTrueChunkStep10Coordinate103
  | 104 => insulinTrueChunkStep10Coordinate104
  | 105 => insulinTrueChunkStep10Coordinate105
  | 106 => insulinTrueChunkStep10Coordinate106
  | 107 => insulinTrueChunkStep10Coordinate107
  | 108 => insulinTrueChunkStep10Coordinate108
  | 109 => insulinTrueChunkStep10Coordinate109
  | 110 => insulinTrueChunkStep10Coordinate110
  | 111 => insulinTrueChunkStep10Coordinate111
  | 112 => insulinTrueChunkStep10Coordinate112
  | 113 => insulinTrueChunkStep10Coordinate113
  | 114 => insulinTrueChunkStep10Coordinate114
  | 115 => insulinTrueChunkStep10Coordinate115
  | 116 => insulinTrueChunkStep10Coordinate116
  | 117 => insulinTrueChunkStep10Coordinate117
  | 118 => insulinTrueChunkStep10Coordinate118
  | 119 => insulinTrueChunkStep10Coordinate119
  | 120 => insulinTrueChunkStep10Coordinate120
  | 121 => insulinTrueChunkStep10Coordinate121
  | 122 => insulinTrueChunkStep10Coordinate122
  | 123 => insulinTrueChunkStep10Coordinate123
  | 124 => insulinTrueChunkStep10Coordinate124
  | 125 => insulinTrueChunkStep10Coordinate125
  | 126 => insulinTrueChunkStep10Coordinate126
  | 127 => insulinTrueChunkStep10Coordinate127
  | 128 => insulinTrueChunkStep10Coordinate128
  | 129 => insulinTrueChunkStep10Coordinate129
  | 130 => insulinTrueChunkStep10Coordinate130
  | 131 => insulinTrueChunkStep10Coordinate131
  | 132 => insulinTrueChunkStep10Coordinate132
  | 133 => insulinTrueChunkStep10Coordinate133
  | 134 => insulinTrueChunkStep10Coordinate134
  | 135 => insulinTrueChunkStep10Coordinate135
  | 136 => insulinTrueChunkStep10Coordinate136
  | 137 => insulinTrueChunkStep10Coordinate137
  | 138 => insulinTrueChunkStep10Coordinate138
  | 139 => insulinTrueChunkStep10Coordinate139
  | 140 => insulinTrueChunkStep10Coordinate140
  | 141 => insulinTrueChunkStep10Coordinate141
  | 142 => insulinTrueChunkStep10Coordinate142
  | 143 => insulinTrueChunkStep10Coordinate143
  | 144 => insulinTrueChunkStep10Coordinate144
  | 145 => insulinTrueChunkStep10Coordinate145
  | 146 => insulinTrueChunkStep10Coordinate146
  | 147 => insulinTrueChunkStep10Coordinate147
  | 148 => insulinTrueChunkStep10Coordinate148
  | 149 => insulinTrueChunkStep10Coordinate149
  | 150 => insulinTrueChunkStep10Coordinate150
  | 151 => insulinTrueChunkStep10Coordinate151
  | 152 => insulinTrueChunkStep10Coordinate152
  | 153 => insulinTrueChunkStep10Coordinate153
  | 154 => insulinTrueChunkStep10Coordinate154
  | 155 => insulinTrueChunkStep10Coordinate155
  | 156 => insulinTrueChunkStep10Coordinate156
  | 157 => insulinTrueChunkStep10Coordinate157
  | 158 => insulinTrueChunkStep10Coordinate158
  | 159 => insulinTrueChunkStep10Coordinate159
  | 160 => insulinTrueChunkStep10Coordinate160
  | 161 => insulinTrueChunkStep10Coordinate161
  | 162 => insulinTrueChunkStep10Coordinate162
  | 163 => insulinTrueChunkStep10Coordinate163
  | 164 => insulinTrueChunkStep10Coordinate164
  | 165 => insulinTrueChunkStep10Coordinate165
  | 166 => insulinTrueChunkStep10Coordinate166
  | 167 => insulinTrueChunkStep10Coordinate167
  | 168 => insulinTrueChunkStep10Coordinate168
  | 169 => insulinTrueChunkStep10Coordinate169
  | 170 => insulinTrueChunkStep10Coordinate170
  | 171 => insulinTrueChunkStep10Coordinate171
  | 172 => insulinTrueChunkStep10Coordinate172
  | 173 => insulinTrueChunkStep10Coordinate173
  | 174 => insulinTrueChunkStep10Coordinate174
  | 175 => insulinTrueChunkStep10Coordinate175
  | 176 => insulinTrueChunkStep10Coordinate176
  | 177 => insulinTrueChunkStep10Coordinate177
  | 178 => insulinTrueChunkStep10Coordinate178
  | 179 => insulinTrueChunkStep10Coordinate179
  | 180 => insulinTrueChunkStep10Coordinate180
  | 181 => insulinTrueChunkStep10Coordinate181
  | 182 => insulinTrueChunkStep10Coordinate182
  | 183 => insulinTrueChunkStep10Coordinate183
  | 184 => insulinTrueChunkStep10Coordinate184
  | 185 => insulinTrueChunkStep10Coordinate185
  | 186 => insulinTrueChunkStep10Coordinate186
  | 187 => insulinTrueChunkStep10Coordinate187
  | 188 => insulinTrueChunkStep10Coordinate188
  | 189 => insulinTrueChunkStep10Coordinate189
  | 190 => insulinTrueChunkStep10Coordinate190
  | 191 => insulinTrueChunkStep10Coordinate191
  | 192 => insulinTrueChunkStep10Coordinate192
  | 193 => insulinTrueChunkStep10Coordinate193
  | 194 => insulinTrueChunkStep10Coordinate194
  | 195 => insulinTrueChunkStep10Coordinate195
  | 196 => insulinTrueChunkStep10Coordinate196
  | 197 => insulinTrueChunkStep10Coordinate197
  | 198 => insulinTrueChunkStep10Coordinate198
  | 199 => insulinTrueChunkStep10Coordinate199
  | 200 => insulinTrueChunkStep10Coordinate200
  | 201 => insulinTrueChunkStep10Coordinate201
  | 202 => insulinTrueChunkStep10Coordinate202
  | 203 => insulinTrueChunkStep10Coordinate203
  | 204 => insulinTrueChunkStep10Coordinate204
  | 205 => insulinTrueChunkStep10Coordinate205
  | 206 => insulinTrueChunkStep10Coordinate206
  | 207 => insulinTrueChunkStep10Coordinate207
  | 208 => insulinTrueChunkStep10Coordinate208
  | 209 => insulinTrueChunkStep10Coordinate209
  | 210 => insulinTrueChunkStep10Coordinate210
  | 211 => insulinTrueChunkStep10Coordinate211
  | 212 => insulinTrueChunkStep10Coordinate212
  | 213 => insulinTrueChunkStep10Coordinate213
  | 214 => insulinTrueChunkStep10Coordinate214
  | 215 => insulinTrueChunkStep10Coordinate215
  | 216 => insulinTrueChunkStep10Coordinate216
  | 217 => insulinTrueChunkStep10Coordinate217
  | 218 => insulinTrueChunkStep10Coordinate218
  | 219 => insulinTrueChunkStep10Coordinate219
  | 220 => insulinTrueChunkStep10Coordinate220
  | 221 => insulinTrueChunkStep10Coordinate221
  | 222 => insulinTrueChunkStep10Coordinate222
  | 223 => insulinTrueChunkStep10Coordinate223
  | 224 => insulinTrueChunkStep10Coordinate224
  | 225 => insulinTrueChunkStep10Coordinate225
  | 226 => insulinTrueChunkStep10Coordinate226
  | 227 => insulinTrueChunkStep10Coordinate227
  | 228 => insulinTrueChunkStep10Coordinate228
  | 229 => insulinTrueChunkStep10Coordinate229
  | 230 => insulinTrueChunkStep10Coordinate230
  | 231 => insulinTrueChunkStep10Coordinate231
  | 232 => insulinTrueChunkStep10Coordinate232
  | 233 => insulinTrueChunkStep10Coordinate233
  | 234 => insulinTrueChunkStep10Coordinate234
  | 235 => insulinTrueChunkStep10Coordinate235
  | 236 => insulinTrueChunkStep10Coordinate236
  | 237 => insulinTrueChunkStep10Coordinate237
  | 238 => insulinTrueChunkStep10Coordinate238
  | 239 => insulinTrueChunkStep10Coordinate239
  | 240 => insulinTrueChunkStep10Coordinate240
  | 241 => insulinTrueChunkStep10Coordinate241
  | 242 => insulinTrueChunkStep10Coordinate242
  | 243 => insulinTrueChunkStep10Coordinate243
  | 244 => insulinTrueChunkStep10Coordinate244
  | 245 => insulinTrueChunkStep10Coordinate245
  | 246 => insulinTrueChunkStep10Coordinate246
  | 247 => insulinTrueChunkStep10Coordinate247
  | 248 => insulinTrueChunkStep10Coordinate248
  | 249 => insulinTrueChunkStep10Coordinate249
  | 250 => insulinTrueChunkStep10Coordinate250
  | 251 => insulinTrueChunkStep10Coordinate251
  | 252 => insulinTrueChunkStep10Coordinate252
  | 253 => insulinTrueChunkStep10Coordinate253
  | 254 => insulinTrueChunkStep10Coordinate254
  | 255 => insulinTrueChunkStep10Coordinate255
  | 256 => insulinTrueChunkStep10Coordinate256
  | 257 => insulinTrueChunkStep10Coordinate257
  | 258 => insulinTrueChunkStep10Coordinate258
  | 259 => insulinTrueChunkStep10Coordinate259
  | 260 => insulinTrueChunkStep10Coordinate260
  | 261 => insulinTrueChunkStep10Coordinate261
  | 262 => insulinTrueChunkStep10Coordinate262
  | 263 => insulinTrueChunkStep10Coordinate263
  | 264 => insulinTrueChunkStep10Coordinate264
  | 265 => insulinTrueChunkStep10Coordinate265
  | 266 => insulinTrueChunkStep10Coordinate266
  | 267 => insulinTrueChunkStep10Coordinate267
  | 268 => insulinTrueChunkStep10Coordinate268
  | 269 => insulinTrueChunkStep10Coordinate269
  | 270 => insulinTrueChunkStep10Coordinate270
  | 271 => insulinTrueChunkStep10Coordinate271
  | 272 => insulinTrueChunkStep10Coordinate272
  | 273 => insulinTrueChunkStep10Coordinate273
  | 274 => insulinTrueChunkStep10Coordinate274
  | 275 => insulinTrueChunkStep10Coordinate275
  | 276 => insulinTrueChunkStep10Coordinate276
  | 277 => insulinTrueChunkStep10Coordinate277
  | 278 => insulinTrueChunkStep10Coordinate278
  | 279 => insulinTrueChunkStep10Coordinate279
  | 280 => insulinTrueChunkStep10Coordinate280
  | 281 => insulinTrueChunkStep10Coordinate281
  | 282 => insulinTrueChunkStep10Coordinate282
  | 283 => insulinTrueChunkStep10Coordinate283
  | 284 => insulinTrueChunkStep10Coordinate284
  | 285 => insulinTrueChunkStep10Coordinate285
  | 286 => insulinTrueChunkStep10Coordinate286
  | 287 => insulinTrueChunkStep10Coordinate287
  | 288 => insulinTrueChunkStep10Coordinate288
  | 289 => insulinTrueChunkStep10Coordinate289
  | 290 => insulinTrueChunkStep10Coordinate290
  | 291 => insulinTrueChunkStep10Coordinate291
  | 292 => insulinTrueChunkStep10Coordinate292
  | 293 => insulinTrueChunkStep10Coordinate293
  | 294 => insulinTrueChunkStep10Coordinate294
  | 295 => insulinTrueChunkStep10Coordinate295
  | 296 => insulinTrueChunkStep10Coordinate296
  | 297 => insulinTrueChunkStep10Coordinate297
  | 298 => insulinTrueChunkStep10Coordinate298
  | 299 => insulinTrueChunkStep10Coordinate299
  | 300 => insulinTrueChunkStep10Coordinate300
  | 301 => insulinTrueChunkStep10Coordinate301
  | 302 => insulinTrueChunkStep10Coordinate302
  | 303 => insulinTrueChunkStep10Coordinate303
  | 304 => insulinTrueChunkStep10Coordinate304
  | 305 => insulinTrueChunkStep10Coordinate305
  | 306 => insulinTrueChunkStep10Coordinate306
  | 307 => insulinTrueChunkStep10Coordinate307
  | 308 => insulinTrueChunkStep10Coordinate308
  | 309 => insulinTrueChunkStep10Coordinate309
  | 310 => insulinTrueChunkStep10Coordinate310
  | 311 => insulinTrueChunkStep10Coordinate311
  | 312 => insulinTrueChunkStep10Coordinate312
  | 313 => insulinTrueChunkStep10Coordinate313
  | 314 => insulinTrueChunkStep10Coordinate314
  | 315 => insulinTrueChunkStep10Coordinate315
  | 316 => insulinTrueChunkStep10Coordinate316
  | 317 => insulinTrueChunkStep10Coordinate317
  | 318 => insulinTrueChunkStep10Coordinate318
  | 319 => insulinTrueChunkStep10Coordinate319
  | 320 => insulinTrueChunkStep10Coordinate320
  | 321 => insulinTrueChunkStep10Coordinate321
  | 322 => insulinTrueChunkStep10Coordinate322
  | 323 => insulinTrueChunkStep10Coordinate323
  | 324 => insulinTrueChunkStep10Coordinate324
  | 325 => insulinTrueChunkStep10Coordinate325
  | 326 => insulinTrueChunkStep10Coordinate326
  | 327 => insulinTrueChunkStep10Coordinate327
  | 328 => insulinTrueChunkStep10Coordinate328
  | 329 => insulinTrueChunkStep10Coordinate329
  | 330 => insulinTrueChunkStep10Coordinate330
  | 331 => insulinTrueChunkStep10Coordinate331
  | 332 => insulinTrueChunkStep10Coordinate332
  | 333 => insulinTrueChunkStep10Coordinate333
  | 334 => insulinTrueChunkStep10Coordinate334
  | 335 => insulinTrueChunkStep10Coordinate335
  | 336 => insulinTrueChunkStep10Coordinate336
  | 337 => insulinTrueChunkStep10Coordinate337
  | 338 => insulinTrueChunkStep10Coordinate338
  | 339 => insulinTrueChunkStep10Coordinate339
  | 340 => insulinTrueChunkStep10Coordinate340
  | 341 => insulinTrueChunkStep10Coordinate341
  | 342 => insulinTrueChunkStep10Coordinate342
  | 343 => insulinTrueChunkStep10Coordinate343
  | 344 => insulinTrueChunkStep10Coordinate344
  | 345 => insulinTrueChunkStep10Coordinate345
  | 346 => insulinTrueChunkStep10Coordinate346
  | 347 => insulinTrueChunkStep10Coordinate347
  | 348 => insulinTrueChunkStep10Coordinate348
  | 349 => insulinTrueChunkStep10Coordinate349
  | 350 => insulinTrueChunkStep10Coordinate350
  | 351 => insulinTrueChunkStep10Coordinate351
  | 352 => insulinTrueChunkStep10Coordinate352
  | 353 => insulinTrueChunkStep10Coordinate353
  | 354 => insulinTrueChunkStep10Coordinate354
  | 355 => insulinTrueChunkStep10Coordinate355
  | 356 => insulinTrueChunkStep10Coordinate356
  | 357 => insulinTrueChunkStep10Coordinate357
  | 358 => insulinTrueChunkStep10Coordinate358
  | _ => insulinTrueChunkStep10Coordinate359

end CausalSmith.Stat.PomdpLatentOverlapMinimax
