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
    g⁻¹ * n * g ∈ N := by
  have h := conj_mem n hn g⁻¹
  rw [inv_inv] at h
  exact h

instance center_normal : (center G).Normal where
  conj_mem := by
    intro z hz g
    rw [hz g]
    rw [mul_assoc]
    rw [mul_inv_cancel]
    rw [mul_one]
    exact hz

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
