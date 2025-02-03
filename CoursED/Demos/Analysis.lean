-- import GlimpseOfLean.Library.Basic
import Mathlib

namespace analysis

/-- A sequence `u` of real numbers converges to `l` if `∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| ≤ ε`.
This condition will be spelled `seq_limit u l`. -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-- A function`f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`.
This condition will be spelled `continuous_at f x₀`.-/
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

/-- Now we claim that if `f` is continuous at `x₀` then it is sequentially continuous
at `x₀`: for any sequence `u` converging to `x₀`, the sequence `f ∘ u` converges
to `f x₀`.  -/
theorem composition_example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
    seq_limit (f ∘ u) (f x₀) := by

  unfold seq_limit at *
  unfold continuous_at at *

  intro ε hε

  #check hf ε hε

  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε

  #check hu δ δ_pos

  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos

  use N

  intros n hn

  apply Hf

  exact Hu n hn

#print axioms composition_example

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
    seq_limit (f ∘ u) (f x₀) := by

  intro ε hε

  specialize hf ε hε

  obtain ⟨δ, hδ, hf⟩ := hf

  specialize hu δ hδ

  obtain ⟨N, hN⟩ := hu

  use N

  intro n hn

  specialize hN n hn

  specialize hf (u n)
  exact hf hN

-- More idiomatic

variable {f : ℝ → ℝ} {u : ℕ → ℝ} {x₀ : ℝ}

open Filter Topology

example (hu : Tendsto u atTop (𝓝 x₀)) (hf : ContinuousAt f x₀) :
    Tendsto (f ∘ u) atTop (𝓝 (f x₀)) :=
  Tendsto.comp hf hu

-- Unfolding the idiomatic version

#check Filter

example (hu : Tendsto u atTop (𝓝 x₀)) (hf : ContinuousAt f x₀) :
    Tendsto (f ∘ u) atTop (𝓝 (f x₀)) := by
  unfold Tendsto
  intro s hs
  rw [Filter.mem_map]
  rw [Set.preimage_comp]

  rw [Tendsto] at hu
  change (𝓝 x₀).sets ⊆ (map u atTop).sets at hu
  apply hu

  rw [ContinuousAt, Tendsto] at hf
  apply hf

  exact hs

example (hu : Tendsto u atTop (𝓝 x₀)) (hf : ContinuousAt f x₀) :
    Tendsto (f ∘ u) atTop (𝓝 (f x₀)) :=
  fun _ hs => hu (hf hs)

end analysis
