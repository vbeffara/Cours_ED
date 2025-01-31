import Mathlib

namespace algebra

class group (G : Type) where
  mul : G → G → G
  e : G
  inv : G → G
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  neutl : ∀ a, mul e a = a
  neutr : ∀ a, mul a e = a
  mulinv : ∀ a, mul a (inv a) = e

open group

variable {G : Type} [group G]

theorem inv_unique {a b : G} (h : mul b a = e) : b = inv a := by
  have h1 : mul a (inv a) = e := mulinv a
  have h2 : mul b (mul a (inv a)) = mul b e := by
    rw [h1]
  rw [neutr] at h2
  rw [← assoc] at h2
  rw [h] at h2
  rw [neutl] at h2
  exact h2.symm

example {a : G} : group.mul (group.inv a) a = group.e := by
  sorry

end algebra
