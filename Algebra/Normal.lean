import Algebra.Subgroup

universe u v

namespace Algebra

open Group

namespace Subgroup

variable {G : Type u} [Group G]

class Normal (N : Subgroup G) : Prop where
  conj_mem : ∀ n : G, n ∈ N → ∀ g : G, g * n * g⁻¹ ∈ N

-- conjugating the other way round also stays in N
theorem Normal.conj_mem' (N : Subgroup G) [N.Normal] (n : G) (hn : n ∈ N) (g : G) :
    g⁻¹ * n * g ∈ N :=
  sorry

instance bot_normal : (bot G).Normal :=
  sorry

instance top_normal : (top G).Normal :=
  sorry

instance inter_normal (S T : Subgroup G) [S.Normal] [T.Normal] : (inter S T).Normal :=
  sorry

end Subgroup

namespace Hom

variable {G : Type u} {H : Type v} [Group G] [Group H]

instance ker_normal (f : G →* H) : (ker f).Normal :=
  sorry

end Hom
end Algebra
