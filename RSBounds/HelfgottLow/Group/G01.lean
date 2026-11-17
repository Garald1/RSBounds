import RSBounds.HelfgottLow.Chunk.C0050
import RSBounds.HelfgottLow.Chunk.C0051
import RSBounds.HelfgottLow.Chunk.C0052
import RSBounds.HelfgottLow.Chunk.C0053
import RSBounds.HelfgottLow.Chunk.C0054
import RSBounds.HelfgottLow.Chunk.C0055
import RSBounds.HelfgottLow.Chunk.C0056
import RSBounds.HelfgottLow.Chunk.C0057
import RSBounds.HelfgottLow.Chunk.C0058
import RSBounds.HelfgottLow.Chunk.C0059
import RSBounds.HelfgottLow.Chunk.C0060
import RSBounds.HelfgottLow.Chunk.C0061
import RSBounds.HelfgottLow.Chunk.C0062
import RSBounds.HelfgottLow.Chunk.C0063
import RSBounds.HelfgottLow.Chunk.C0064
import RSBounds.HelfgottLow.Chunk.C0065
import RSBounds.HelfgottLow.Chunk.C0066
import RSBounds.HelfgottLow.Chunk.C0067
import RSBounds.HelfgottLow.Chunk.C0068
import RSBounds.HelfgottLow.Chunk.C0069
import RSBounds.HelfgottLow.Chunk.C0070
import RSBounds.HelfgottLow.Chunk.C0071
import RSBounds.HelfgottLow.Chunk.C0072
import RSBounds.HelfgottLow.Chunk.C0073
import RSBounds.HelfgottLow.Chunk.C0074
import RSBounds.HelfgottLow.Chunk.C0075
import RSBounds.HelfgottLow.Chunk.C0076
import RSBounds.HelfgottLow.Chunk.C0077
import RSBounds.HelfgottLow.Chunk.C0078
import RSBounds.HelfgottLow.Chunk.C0079
import RSBounds.HelfgottLow.Chunk.C0080
import RSBounds.HelfgottLow.Chunk.C0081
import RSBounds.HelfgottLow.Chunk.C0082
import RSBounds.HelfgottLow.Chunk.C0083
import RSBounds.HelfgottLow.Chunk.C0084
import RSBounds.HelfgottLow.Chunk.C0085
import RSBounds.HelfgottLow.Chunk.C0086
import RSBounds.HelfgottLow.Chunk.C0087
import RSBounds.HelfgottLow.Chunk.C0088
import RSBounds.HelfgottLow.Chunk.C0089
import RSBounds.HelfgottLow.Chunk.C0090
import RSBounds.HelfgottLow.Chunk.C0091
import RSBounds.HelfgottLow.Chunk.C0092
import RSBounds.HelfgottLow.Chunk.C0093
import RSBounds.HelfgottLow.Chunk.C0094
import RSBounds.HelfgottLow.Chunk.C0095
import RSBounds.HelfgottLow.Chunk.C0096
import RSBounds.HelfgottLow.Chunk.C0097
import RSBounds.HelfgottLow.Chunk.C0098
import RSBounds.HelfgottLow.Chunk.C0099

/-! Walk chunks 50 to 99. -/

namespace RSBounds.HelfgottLow

theorem group_1 (t : Nat) (ht : t < 50) : ChunkGood (50 + t) :=
  match t, ht with
  | 0, _ => chunk_50
  | 1, _ => chunk_51
  | 2, _ => chunk_52
  | 3, _ => chunk_53
  | 4, _ => chunk_54
  | 5, _ => chunk_55
  | 6, _ => chunk_56
  | 7, _ => chunk_57
  | 8, _ => chunk_58
  | 9, _ => chunk_59
  | 10, _ => chunk_60
  | 11, _ => chunk_61
  | 12, _ => chunk_62
  | 13, _ => chunk_63
  | 14, _ => chunk_64
  | 15, _ => chunk_65
  | 16, _ => chunk_66
  | 17, _ => chunk_67
  | 18, _ => chunk_68
  | 19, _ => chunk_69
  | 20, _ => chunk_70
  | 21, _ => chunk_71
  | 22, _ => chunk_72
  | 23, _ => chunk_73
  | 24, _ => chunk_74
  | 25, _ => chunk_75
  | 26, _ => chunk_76
  | 27, _ => chunk_77
  | 28, _ => chunk_78
  | 29, _ => chunk_79
  | 30, _ => chunk_80
  | 31, _ => chunk_81
  | 32, _ => chunk_82
  | 33, _ => chunk_83
  | 34, _ => chunk_84
  | 35, _ => chunk_85
  | 36, _ => chunk_86
  | 37, _ => chunk_87
  | 38, _ => chunk_88
  | 39, _ => chunk_89
  | 40, _ => chunk_90
  | 41, _ => chunk_91
  | 42, _ => chunk_92
  | 43, _ => chunk_93
  | 44, _ => chunk_94
  | 45, _ => chunk_95
  | 46, _ => chunk_96
  | 47, _ => chunk_97
  | 48, _ => chunk_98
  | 49, _ => chunk_99
  | _ + 50, h => absurd h (by omega)

end RSBounds.HelfgottLow
