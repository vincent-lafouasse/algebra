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

-- the key lemma for the quotient group: b * a = b * (a * b) * b⁻¹
theorem Normal.mem_comm (N : Subgroup G) [N.Normal] {a b : G} (h : a * b ∈ N) : b * a ∈ N :=
  sorry

instance center_normal : (center G).Normal where
  conj_mem := by
    intro z hz g
    rw [hz g]
    rw [mul_inv_cancel_right]
    exact hz

instance bot_normal : (bot G).Normal where
  conj_mem := by
    intro z hz g
    rw [mem_bot] at hz ⊢
    rw [hz, mul_one]
    exact mul_inv_cancel g

instance top_normal : (top G).Normal where
  conj_mem := by
    intro z hz g
    rw [mem_top]
    trivial

instance inter_normal (S T : Subgroup G) [S.Normal] [T.Normal] : (inter S T).Normal where
  conj_mem := by
    intro z hz g
    rw [mem_inter] at hz ⊢
    have hs := Normal.conj_mem z hz.1 g
    have ht := Normal.conj_mem z hz.2 g
    exact ⟨hs, ht⟩

end Subgroup

namespace Hom

variable {G : Type u} {H : Type v} [Group G] [Group H]

instance ker_normal (f : G →* H) : (ker f).Normal where
  conj_mem := by
    intro z hz g
    rw [mem_ker f] at hz ⊢
    rw [map_conj]
    rw [hz, mul_one]
    rw [mul_inv_cancel]

-- needs surjectivity, so it can't be an instance
theorem map_normal (f : G →* H) (hf : Function.Surjective f)
    (S : Subgroup G) [S.Normal] : (map f S).Normal where
  conj_mem := by
    intro n
    simp only [mem_map]
    intro h g
    obtain ⟨a, ha⟩ := h
    obtain ⟨x, hx⟩ := hf g
    rw [← hx]
    rw [← ha.2]
    rw [← map_inv]
    rw [← map_mul]
    rw [← map_mul]
    refine ⟨x * a * x⁻¹, ?_⟩
    refine ⟨?_, rfl⟩
    exact Subgroup.Normal.conj_mem a ha.1 x

instance comap_normal (f : G →* H) (T : Subgroup H) [T.Normal] :
    (comap f T).Normal where
  conj_mem := by
    intro n hn g
    simp only [mem_comap]
    simp only [map_conj]
    exact Subgroup.Normal.conj_mem (f n) hn (f g)

end Hom
end Algebra
