import data.real.basic
import algebra.group.pi
import tuto_lib

notation `|`x`|` := abs x

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers. 
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.

A sequence u is a function from ℕ to ℝ, hence Lean says
u : ℕ → ℝ
The definition we'll be using is:

-- Definition of « u tends to l »
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

Note the use of `∀ ε > 0, ...` which is an abbreviation of
`∀ ε, ε > 0 → ... `

In particular, a statement like `h : ∀ ε > 0, ...`
can be specialized to a given ε₀ by
  `specialize h ε₀ hε₀`
where hε₀ is a proof of ε₀ > 0.

Also recall that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by` (followed by curly braces
if you need more than one tactic invocation).
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, ...

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.

We'll take this opportunity to use two new tactics:

`norm_num` will perform numerical normalization on the goal and `norm_num at h` 
will do the same in assumption `h`. This will get rid of trivial calculations on numbers,
like replacing |l - l| by zero in the next exercise.

`congr'` will try to prove equalities between applications of functions by recursively 
proving the arguments are the same. 
For instance, if the goal is `f x + g y = f z + g t` then congr will replace it by
two goals: `x = z` and `y = t`.
You can limit the recursion depth by specifying a natural number after `congr'`. 
For instance, in the above example, `congr' 1` will give new goals
`f x = f z` and `g y = g t`, which only inspect arguments of the addition and not deeper.
-/

variables (u v w : ℕ → ℝ) (l l' : ℝ)

-- If u is constant with value l then u tends to l
-- 0033
example : (∀ n, u n = l) → seq_limit u l :=
begin
  intros h,
  unfold seq_limit,
  intros ε ε_pos,
  use 1,
  intros n hn,
  rw h,
  norm_num,
  exact le_of_lt ε_pos,
end

/- When dealing with absolute values, we'll use lemmas:

abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub_comm (x y : ℝ) : |x - y| = |y - x|

You should probably write them down on a sheet of paper that you keep at 
hand since they are used in many exercises.
-/

-- Assume l > 0. Then u tends to l implies u n ≥ l/2 for large enough n
-- 0034
example (hl : l > 0) : seq_limit u l → ∃ N, ∀ n ≥ N, u n ≥ l/2 :=
begin
  intros h,
  unfold seq_limit at h,
  have h₁ : (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |u n - l| ≤ l / 2),
  { apply h (l/2), linarith, },
  have key : ∀ (n : ℕ), |(u n)-l| ≤ l/2 → u n ≥ l/2,
  { intros n hn,
    rw [abs_sub_comm, abs_le] at hn,
    cases hn with _ _,
    { by linarith, },
  },
  rcases h₁ with ⟨N₀, hn⟩,
  use N₀,
  intros n hngtN₀,
  apply key n,
  exact hn n hngtN₀,
end

/- 
When dealing with max, you can use

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

You should probably add them to the sheet of paper where you wrote 
the `abs` lemmas since they are used in many exercises.

Let's see an example.
-/

-- If u tends to l and v tends l' then u+v tends to l+l'
example (hu : seq_limit u l) (hv : seq_limit v l') :
seq_limit (u + v) (l + l') :=
begin
  intros ε ε_pos,
  cases hu (ε/2) (by linarith) with N₁ hN₁,
  cases hv (ε/2) (by linarith) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  cases ge_max_iff.mp hn with hn₁ hn₂, 
  have fact₁ : |u n - l| ≤ ε/2,
    from hN₁ n (by linarith),  -- note the use of `from`.
                               -- This is an alias for `exact`, 
                               -- but reads nicer in this context 
  have fact₂ : |v n - l'| ≤ ε/2,
    from hN₂ n (by linarith), 
  calc
  |(u + v) n - (l + l')| = |u n + v n - (l + l')|   : rfl
                     ... = |(u n - l) + (v n - l')| : by congr' 1 ; ring
                     ... ≤ |u n - l| + |v n - l'|   : by apply abs_add
                     ... ≤  ε                       : by linarith,
end

/-
In the above proof, we used `have` to prepare facts for `linarith` consumption in the last line.
Since we have direct proof terms for them, we can feed them directly to `linarith` as in the next proof
of the same statement.
Another variation we introduce is rewriting using `ge_max_iff` and letting `linarith` handle the
conjunction, instead of creating two new assumptions.
-/

example (hu : seq_limit u l) (hv : seq_limit v l') :
seq_limit (u + v) (l + l') :=
begin
  intros ε ε_pos,
  cases hu (ε/2) (by linarith) with N₁ hN₁,
  cases hv (ε/2) (by linarith) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  rw ge_max_iff at hn,
  calc
  |(u + v) n - (l + l')| = |u n + v n - (l + l')|   : rfl
                     ... = |(u n - l) + (v n - l')| : by congr' 1 ; ring
                     ... ≤ |u n - l| + |v n - l'|   : by apply abs_add
                     ... ≤  ε                       : by linarith [hN₁ n (by linarith), hN₂ n (by linarith)],
end

/- Let's do something similar: the squeezing theorem. -/
-- 0035
example (hu : seq_limit u l) (hw : seq_limit w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : seq_limit v l :=
begin
  intros ε ε_pos,
  cases hu ε (by linarith) with N₁ hN₁,
  cases hw ε (by linarith) with N₂ hN₂,
  use (max N₁ N₂),
  intros n hn,
  rw ge_max_iff at hn,
  specialize hN₁ n hn.1, 
  specialize hN₂ n hn.2, 
  have fact₁ : u n - l ≥ -ε,
    from (abs_le.mp hN₁).left,
  have fact₂ : w n - l ≤ ε,
    from (abs_le.mp hN₂).right,
  have key : -ε ≤ v n - l ∧ v n - l ≤ ε,
  { split,
    calc -ε ≤ u n - l      : fact₁
    ... ≤ v n - l          : by linarith [h n], 
    calc v n - l ≤ w n - l : by linarith [h' n]
    ... ≤ ε                : fact₂, },
    exact abs_le.mpr key,
end

/- What about < ε? -/
-- 0036
example (u l) : seq_limit u l ↔
 ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε :=
begin
  unfold seq_limit,
  split,
  { intros hlim ε ε_pos,
    specialize hlim (ε/2) (by linarith),
    cases hlim with N hlim,
    use N,
    intros n hnN,
    specialize hlim n hnN,
    by linarith,
  },
  { intros hlim ε ε_pos,
    specialize hlim ε ε_pos,
    cases hlim with N hlim,
    use N,
    intros n hnN,
    from le_of_lt (hlim n hnN),
  },
end

/- In the next exercise, we'll use

eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y
-/

-- A sequence admits at most one limit
-- 0037
example : seq_limit u l → seq_limit u l' → l = l' :=
begin
  intros hul hul',
  unfold seq_limit at *,
  apply eq_of_abs_sub_le_all,
  intros ε ε_pos,
  specialize hul (ε/2) (by linarith),
  specialize hul' (ε/2) (by linarith),
  cases hul with N hul,
  cases hul' with N' hul',
  specialize hul (N+N') (by linarith),
  specialize hul' (N+N') (by linarith),
  rw abs_sub_comm at hul,
  calc |l - l'| = |l - u (N + N') + (u (N + N') - l')| : by ring_nf
  ... ≤ |l - u (N + N')| + |u (N + N') - l'|           : abs_add (l - u (N + N')) (u (N + N') - l')
  ... ≤ (ε/2) + (ε/2)                                  : by linarith [hul, hul']
  ... = ε                                              : by ring,
end

/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- 0038
example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) :
seq_limit u M :=
begin
  unfold non_decreasing at h',
  intros ε ε_pos,
  cases h with hup heq,
  specialize heq ε ε_pos,
  cases heq with N heq,
  use N,
  intros n hnN,
  have low_bound : n ≥ N → u n - M ≥ -ε,
  { intros hnN,
    calc u n - M ≥ u N - M : by linarith [h' N n hnN]
    ... ≥ -ε               : by linarith [heq],},
  have up_bound : n ≥ N → u n - M ≤ ε,
  { intros hnN, linarith [hup n], },
  rw abs_le,
  exact ⟨low_bound hnN, up_bound hnN⟩,
end

