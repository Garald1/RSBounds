import RSBounds.HelfgottSmall.Chunk.C0150
import RSBounds.HelfgottSmall.Chunk.C0151
import RSBounds.HelfgottSmall.Chunk.C0152
import RSBounds.HelfgottSmall.Chunk.C0153
import RSBounds.HelfgottSmall.Chunk.C0154
import RSBounds.HelfgottSmall.Chunk.C0155
import RSBounds.HelfgottSmall.Chunk.C0156
import RSBounds.HelfgottSmall.Chunk.C0157
import RSBounds.HelfgottSmall.Chunk.C0158
import RSBounds.HelfgottSmall.Chunk.C0159
import RSBounds.HelfgottSmall.Chunk.C0160
import RSBounds.HelfgottSmall.Chunk.C0161
import RSBounds.HelfgottSmall.Chunk.C0162
import RSBounds.HelfgottSmall.Chunk.C0163
import RSBounds.HelfgottSmall.Chunk.C0164
import RSBounds.HelfgottSmall.Chunk.C0165
import RSBounds.HelfgottSmall.Chunk.C0166
import RSBounds.HelfgottSmall.Chunk.C0167
import RSBounds.HelfgottSmall.Chunk.C0168
import RSBounds.HelfgottSmall.Chunk.C0169
import RSBounds.HelfgottSmall.Chunk.C0170
import RSBounds.HelfgottSmall.Chunk.C0171
import RSBounds.HelfgottSmall.Chunk.C0172
import RSBounds.HelfgottSmall.Chunk.C0173
import RSBounds.HelfgottSmall.Chunk.C0174
import RSBounds.HelfgottSmall.Chunk.C0175
import RSBounds.HelfgottSmall.Chunk.C0176
import RSBounds.HelfgottSmall.Chunk.C0177
import RSBounds.HelfgottSmall.Chunk.C0178
import RSBounds.HelfgottSmall.Chunk.C0179
import RSBounds.HelfgottSmall.Chunk.C0180
import RSBounds.HelfgottSmall.Chunk.C0181
import RSBounds.HelfgottSmall.Chunk.C0182
import RSBounds.HelfgottSmall.Chunk.C0183
import RSBounds.HelfgottSmall.Chunk.C0184
import RSBounds.HelfgottSmall.Chunk.C0185
import RSBounds.HelfgottSmall.Chunk.C0186
import RSBounds.HelfgottSmall.Chunk.C0187
import RSBounds.HelfgottSmall.Chunk.C0188
import RSBounds.HelfgottSmall.Chunk.C0189
import RSBounds.HelfgottSmall.Chunk.C0190
import RSBounds.HelfgottSmall.Chunk.C0191
import RSBounds.HelfgottSmall.Chunk.C0192
import RSBounds.HelfgottSmall.Chunk.C0193
import RSBounds.HelfgottSmall.Chunk.C0194
import RSBounds.HelfgottSmall.Chunk.C0195
import RSBounds.HelfgottSmall.Chunk.C0196
import RSBounds.HelfgottSmall.Chunk.C0197
import RSBounds.HelfgottSmall.Chunk.C0198
import RSBounds.HelfgottSmall.Chunk.C0199

/-! Walk chunks 150 to 199. -/

namespace RSBounds.HelfgottSmall

theorem group_3 (t : Nat) (ht : t < 50) : ChunkGood (150 + t) :=
  match t, ht with
  | 0, _ => chunk_150
  | 1, _ => chunk_151
  | 2, _ => chunk_152
  | 3, _ => chunk_153
  | 4, _ => chunk_154
  | 5, _ => chunk_155
  | 6, _ => chunk_156
  | 7, _ => chunk_157
  | 8, _ => chunk_158
  | 9, _ => chunk_159
  | 10, _ => chunk_160
  | 11, _ => chunk_161
  | 12, _ => chunk_162
  | 13, _ => chunk_163
  | 14, _ => chunk_164
  | 15, _ => chunk_165
  | 16, _ => chunk_166
  | 17, _ => chunk_167
  | 18, _ => chunk_168
  | 19, _ => chunk_169
  | 20, _ => chunk_170
  | 21, _ => chunk_171
  | 22, _ => chunk_172
  | 23, _ => chunk_173
  | 24, _ => chunk_174
  | 25, _ => chunk_175
  | 26, _ => chunk_176
  | 27, _ => chunk_177
  | 28, _ => chunk_178
  | 29, _ => chunk_179
  | 30, _ => chunk_180
  | 31, _ => chunk_181
  | 32, _ => chunk_182
  | 33, _ => chunk_183
  | 34, _ => chunk_184
  | 35, _ => chunk_185
  | 36, _ => chunk_186
  | 37, _ => chunk_187
  | 38, _ => chunk_188
  | 39, _ => chunk_189
  | 40, _ => chunk_190
  | 41, _ => chunk_191
  | 42, _ => chunk_192
  | 43, _ => chunk_193
  | 44, _ => chunk_194
  | 45, _ => chunk_195
  | 46, _ => chunk_196
  | 47, _ => chunk_197
  | 48, _ => chunk_198
  | 49, _ => chunk_199
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
