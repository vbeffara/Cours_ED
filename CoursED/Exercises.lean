import Mathlib
import CoursED.Demos

namespace topology

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def continuous (f : ℝ → ℝ) : Prop :=
  ∀ x, continuous_at f x

def unif_limit (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |F n x - f x| ≤ ε

theorem continuous_limit (F : ℕ → (ℝ → ℝ)) (f : ℝ → ℝ) (h_F : ∀ n, continuous (F n))
    (h_lim : unif_limit F f) : continuous f := by
  intro x₀ ε hε
  have ε_3_pos : ε / 3 > 0 := by positivity
  obtain ⟨N, hN⟩ := h_lim (ε / 3) ε_3_pos
  obtain ⟨δ, hδ, l0⟩ := h_F N x₀ (ε / 3) ε_3_pos
  use δ
  constructor
  · assumption
  · intro x hx
    have l1 := abs_add (f x - F N x) (F N x - f x₀)
    have l2 := abs_add (F N x - F N x₀) (F N x₀ - f x₀)
    simp at l1 l2
    have l3 := hN N le_rfl x
    rw [abs_sub_comm] at l3
    have l8 := hN N le_rfl x₀
    have l9 := l0 x hx
    linarith

theorem continuous_iff (f : ℝ → ℝ) (x₀ : ℝ) : continuous_at f x₀ ↔
    (∀ u : ℕ → ℝ, seq_limit u x₀ → seq_limit (f ∘ u) (f x₀)) := by
  constructor
  · intro hf u hu ε hε
    obtain ⟨δ, hδ, h⟩ := hf ε hε
    obtain ⟨N, hN⟩ := hu δ hδ
    use N
    intro n hn
    apply h
    apply hN
    assumption
  · intro h ε hε
    contrapose! h
    -- Define our favorite sequence going to 0
    let v (n : ℕ) : ℝ := 1 / (n + 1)
    have hv1 n : 0 < v n := by positivity
    have hv2 : seq_limit v 0 := by
      intro ε hε
      use Nat.ceil (1 / ε)
      simp [v]
      intro n hn
      have := inv_le_of_inv_le₀ hε hn
      refine le_trans ?_ this
      rw [abs_inv]
      apply inv_anti₀
      · have : 0 < ε⁻¹ := by positivity
        linarith
      · rw [abs_of_nonneg (by positivity)]
        simp
    -- Construct the sequence `u n`
    have key (n : ℕ) : ∃ x : ℝ, |x - x₀| ≤ v n ∧ ε < |f x - f x₀| := h (v n) (hv1 n)
    choose u hu using key -- This does in one go what we painfully constructed together
    use u
    -- Show that it works
    constructor
    · intro ε hε
      obtain ⟨N, hN⟩ := hv2 ε hε
      simp at hN
      use N
      intro n hn
      specialize hN n hn
      rw [abs_of_pos (hv1 n)] at hN
      linarith [(hu n).1]
    · unfold seq_limit
      push_neg
      refine ⟨ε, hε, ?_⟩
      intro N
      exact ⟨N, le_rfl, (hu N).2⟩

end topology

namespace algebra

open group

variable {G : Type} [group G]

theorem group_inv_mul (a b : G) : inv (mul a b) = mul (inv b) (inv a) := by
  symm
  apply inv_unique
  rw [assoc, ← assoc (inv a) a b]
  simp [invl, neutl]

structure group_action (G : Type) [group G] (X : Type) where
  act : G → X → X
  id : ∀ x : X, act e x = x
  assoc : ∀ g₁ g₂ : G, ∀ x : X, act g₁ (act g₂ x) = act (g₁ * g₂) x

example : group_action G G where
  act g h := g * h
  id := by simp ; rfl
  assoc g₁ g₂ x := by simp [assoc']

example : group_action G G where
  act g h := g * h * g⁻¹
  id g := by
    have key : (e : G)⁻¹ = e := by
      symm
      apply inv_unique
      exact neutl e
    simp [key, HMul.hMul, Mul.mul, neutl, neutr] -- unfold notation
  assoc g₁ g₂ g := by group -- tactic for proving group identities

structure subgroup (G : Type) [group G] where
  support : Set G
  id : 1 ∈ support
  mul : ∀ g ∈ support, ∀ h ∈ support, g * h ∈ support
  inv : ∀ g ∈ support, g⁻¹ ∈ support

variable {H : subgroup G}

def related (H : subgroup G) (g₁ g₂ : G) : Prop := g₂ * g₁⁻¹ ∈ H.support

def normal (H : subgroup G) : Prop :=
  ∀ h ∈ H.support, ∀ g : G, g * h * g⁻¹ ∈ H.support

theorem rel_equiv (H : subgroup G) : Equivalence (related H) where
  refl x := by simp [related, H.id]
  symm := by
    unfold related
    intro x y h
    convert H.inv _ h using 1
    group
  trans := by
    unfold related
    rintro x y z h1 h2
    convert H.mul _ h2 _ h1 using 1
    group

def rel_setoid (H : subgroup G) : Setoid G where
  r := related H
  iseqv := rel_equiv H

def quotient (G : Type) [group G] (H : subgroup G) := Quotient (rel_setoid H)

theorem inv_compat (hH : normal H) (rel : related H g₁ g₂) : related H g₁⁻¹ g₂⁻¹ := by
  have := hH _ (H.inv _ rel) g₁⁻¹
  simp at this
  simp [related]
  assumption

-- Multiplication is well-defined on the quotient
theorem key (hH : normal H) {g₁ g₂ h₁ h₂ : G}
    (H1 : related H g₁ g₂) (H2 : related H h₁ h₂) :
    related H (g₁ * h₁) (g₂ * h₂) := by
  unfold related at *
  convert H.mul _ H1 _ (hH _ H2 g₁) using 1
  group

instance (h_normal : normal H) : group (quotient G H) where
  mul := by -- Pass multiplication to the quotient
    apply Quotient.map₂ group.mul
    intro g₁ g₂ H1 h₁ h₂ H2
    exact key h_normal H1 H2
  e := ⟦e⟧
  inv := by
    apply Quotient.map group.inv
    intro x y
    exact inv_compat h_normal
  assoc := by
    #check Quotient.ind
    apply Quotient.ind ; intro a
    apply Quotient.ind ; intro b
    apply Quotient.ind ; intro c
    simp [assoc]
  neutl := by apply Quotient.ind ; simp [neutl]
  neutr := by apply Quotient.ind ; simp [neutr]
  invl := by apply Quotient.ind ; simp [invl]
  invr := by apply Quotient.ind ; simp [invr]

end algebra

namespace induction

inductive nat
| zero : nat
| succ : nat → nat

def add (a : nat) : nat → nat
| nat.zero => a
| nat.succ b => (add a b).succ

def mul (a : nat) : nat → nat
| nat.zero => nat.zero
| nat.succ b => add (mul a b) a

variable {a b : nat}

theorem nat_add_zero : add a nat.zero = a := by
  rfl

theorem nat_zero_add : add nat.zero b = b := by
  induction b with
  | zero => rfl
  | succ b' hr =>
    rw [add]
    rw [hr]

theorem nat_add_comm : add a b = add b a := sorry

theorem nat_mul_comm : mul a b = mul b a := sorry

end induction

namespace arithmetic

def divides (a b : ℕ) := ∃ k, b = a * k

def prime (n : ℕ) := n ≠ 0 ∧ n ≠ 1 ∧ ∀ a, divides a n → a = 1 ∨ a = n

theorem eucl_div (n p : ℕ) (hp : 0 < p) : ∃ q : ℕ, ∃ r : Fin p, n = p * q + r := by
  induction n with
  | zero =>
    use 0
    use ⟨0, hp⟩
    rfl
  | succ n h =>
    obtain ⟨q, r, h⟩ := h
    by_cases hr : r.val + 1 = p
    · use q + 1
      use ⟨0, hp⟩
      simp [h, ← hr]
      ring
    · use q
      refine ⟨⟨r + 1, ?_⟩, ?_⟩
      · have := r.2
        omega
      · simp [h]
        ring

theorem odd_square_form (hn : Odd n) : ∃ k : ℤ, n ^ 2 = 8 * k + 1 := by
  unfold Odd at hn
  obtain ⟨k, hk⟩ := hn
  subst hk
  have h1 := k.even_or_odd
  cases' h1  with h h
  · obtain ⟨l, hl⟩ := h
    subst hl
    ring_nf
    use l + 2 * l ^ 2
    ring
  · obtain ⟨l, rfl⟩ := h
    use 1 + 3 * l + 2 * l ^ 2
    ring

theorem prime_mod (n : ℕ) (hn : prime n) :
    (∃ k, n = 6 * k + 1) ∨ (∃ k, n = 6 * k + 5) := by
  obtain ⟨q, r, rfl⟩ := eucl_div n 6 (by norm_num)
  fin_cases r <;> simp [prime, divides] at * <;> contrapose! hn
  · intro hq
    use 2
    use 3 * q
    omega
  · sorry
  · sorry
  · sorry
  all_goals sorry

theorem infinite_primes : ∀ a, ∃ b > a, prime b := by
  intro n
  let N : ℕ := n.factorial + 1
  have h1 : ∃ p : ℕ, prime p ∧ divides p N := sorry
  obtain ⟨p, hp1, hp2⟩ := h1
  refine ⟨p, ?_, hp1⟩
  contrapose! hp2
  sorry

end arithmetic
