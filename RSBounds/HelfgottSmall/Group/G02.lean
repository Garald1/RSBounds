import RSBounds.HelfgottSmall.Chunk.C0100
import RSBounds.HelfgottSmall.Chunk.C0101
import RSBounds.HelfgottSmall.Chunk.C0102
import RSBounds.HelfgottSmall.Chunk.C0103
import RSBounds.HelfgottSmall.Chunk.C0104
import RSBounds.HelfgottSmall.Chunk.C0105
import RSBounds.HelfgottSmall.Chunk.C0106
import RSBounds.HelfgottSmall.Chunk.C0107
import RSBounds.HelfgottSmall.Chunk.C0108
import RSBounds.HelfgottSmall.Chunk.C0109
import RSBounds.HelfgottSmall.Chunk.C0110
import RSBounds.HelfgottSmall.Chunk.C0111
import RSBounds.HelfgottSmall.Chunk.C0112
import RSBounds.HelfgottSmall.Chunk.C0113
import RSBounds.HelfgottSmall.Chunk.C0114
import RSBounds.HelfgottSmall.Chunk.C0115
import RSBounds.HelfgottSmall.Chunk.C0116
import RSBounds.HelfgottSmall.Chunk.C0117
import RSBounds.HelfgottSmall.Chunk.C0118
import RSBounds.HelfgottSmall.Chunk.C0119
import RSBounds.HelfgottSmall.Chunk.C0120
import RSBounds.HelfgottSmall.Chunk.C0121
import RSBounds.HelfgottSmall.Chunk.C0122
import RSBounds.HelfgottSmall.Chunk.C0123
import RSBounds.HelfgottSmall.Chunk.C0124
import RSBounds.HelfgottSmall.Chunk.C0125
import RSBounds.HelfgottSmall.Chunk.C0126
import RSBounds.HelfgottSmall.Chunk.C0127
import RSBounds.HelfgottSmall.Chunk.C0128
import RSBounds.HelfgottSmall.Chunk.C0129
import RSBounds.HelfgottSmall.Chunk.C0130
import RSBounds.HelfgottSmall.Chunk.C0131
import RSBounds.HelfgottSmall.Chunk.C0132
import RSBounds.HelfgottSmall.Chunk.C0133
import RSBounds.HelfgottSmall.Chunk.C0134
import RSBounds.HelfgottSmall.Chunk.C0135
import RSBounds.HelfgottSmall.Chunk.C0136
import RSBounds.HelfgottSmall.Chunk.C0137
import RSBounds.HelfgottSmall.Chunk.C0138
import RSBounds.HelfgottSmall.Chunk.C0139
import RSBounds.HelfgottSmall.Chunk.C0140
import RSBounds.HelfgottSmall.Chunk.C0141
import RSBounds.HelfgottSmall.Chunk.C0142
import RSBounds.HelfgottSmall.Chunk.C0143
import RSBounds.HelfgottSmall.Chunk.C0144
import RSBounds.HelfgottSmall.Chunk.C0145
import RSBounds.HelfgottSmall.Chunk.C0146
import RSBounds.HelfgottSmall.Chunk.C0147
import RSBounds.HelfgottSmall.Chunk.C0148
import RSBounds.HelfgottSmall.Chunk.C0149

/-! Walk chunks 100 to 149. -/

namespace RSBounds.HelfgottSmall

theorem group_2 (t : Nat) (ht : t < 50) : ChunkGood (100 + t) :=
  match t, ht with
  | 0, _ => chunk_100
  | 1, _ => chunk_101
  | 2, _ => chunk_102
  | 3, _ => chunk_103
  | 4, _ => chunk_104
  | 5, _ => chunk_105
  | 6, _ => chunk_106
  | 7, _ => chunk_107
  | 8, _ => chunk_108
  | 9, _ => chunk_109
  | 10, _ => chunk_110
  | 11, _ => chunk_111
  | 12, _ => chunk_112
  | 13, _ => chunk_113
  | 14, _ => chunk_114
  | 15, _ => chunk_115
  | 16, _ => chunk_116
  | 17, _ => chunk_117
  | 18, _ => chunk_118
  | 19, _ => chunk_119
  | 20, _ => chunk_120
  | 21, _ => chunk_121
  | 22, _ => chunk_122
  | 23, _ => chunk_123
  | 24, _ => chunk_124
  | 25, _ => chunk_125
  | 26, _ => chunk_126
  | 27, _ => chunk_127
  | 28, _ => chunk_128
  | 29, _ => chunk_129
  | 30, _ => chunk_130
  | 31, _ => chunk_131
  | 32, _ => chunk_132
  | 33, _ => chunk_133
  | 34, _ => chunk_134
  | 35, _ => chunk_135
  | 36, _ => chunk_136
  | 37, _ => chunk_137
  | 38, _ => chunk_138
  | 39, _ => chunk_139
  | 40, _ => chunk_140
  | 41, _ => chunk_141
  | 42, _ => chunk_142
  | 43, _ => chunk_143
  | 44, _ => chunk_144
  | 45, _ => chunk_145
  | 46, _ => chunk_146
  | 47, _ => chunk_147
  | 48, _ => chunk_148
  | 49, _ => chunk_149
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottSmall
