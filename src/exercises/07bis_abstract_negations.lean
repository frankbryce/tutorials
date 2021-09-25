import data.real.basic

open_locale classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contradiction` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/

section negation_prop

variables P Q : Prop

-- 0055
example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,
  { intros hPQ hnQ,
    by_contradiction hP,
    exact hnQ (hPQ hP),
  },
  { intros hnQnP hP,
    by_contradiction hnQ,
    exact (hnQnP hnQ) hP,
  },
end

-- 0056
lemma non_imp (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q :=
begin
  split,
  { intros h,
    by_contradiction H,
    by_cases hP : P,
    { by_cases hQ : Q,
      { have : P → Q, { intros _, exact hQ, },
        exact h this,
      },
      { exact H ⟨ hP, hQ ⟩, },
    },
    { by_cases hQ : Q,
      { have : P → Q, { intros _, exact hQ, },
        exact h this,
      },
      { have : P → Q,
        { intros hP',
          exfalso,
          exact hP hP',
        },
        exact h this,
      },
    },
  },
  { intro h,
    by_contradiction H,
    exact h.right (H h.left),
  },
end

-- In the next one, let's use the axiom
-- propext {P Q : Prop} : (P ↔ Q) → P = Q

-- 0057
example (P : Prop) : ¬ P ↔ P = false :=
begin
  split,
  { intros hP,
    apply propext,
    split,
    { intros P, exact hP P, },
    { intros hF, exfalso, exact hF, },
  },
  { intros h h',
    rwa h at h',
  },
end

end negation_prop

section negation_quantifiers
variables (X : Type) (P : X → Prop)

-- 0058
example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  split,
  { intros h,
    by_contradiction H,
    apply h,
    intros x,
    by_contradiction HPx,
    apply H,
    use x,
  },
  { intros h,
    by_contradiction H,
    cases h with x hPx,
    exact hPx (H x),
  },
end

-- 0059
example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  split,
  { intros h,
    by_contradiction H,
    apply H,
    intros x,
    by_contradiction H',
    apply h,
    use x,
    exact H',
  },
  { intros h,
    by_contradiction H,
    cases H with x hx,
    exact (h x) hx,
  },
end

-- 0060
example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  split,
  { intros h ε ε_pos,
    by_contradiction H,
    apply h,
    use ε,
    exact ⟨ ε_pos, H ⟩,
  },
  { intros h,
    by_contradiction H,
    cases H with ε H,
    cases H with ε_pos H,
    exact (h ε ε_pos) H,
  },
end

-- 0061
example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  split,
  { intros h,
    by_contradiction H,
    apply h,
    intros x x_pos,
    by_contradiction HP,
    apply H,
    use [x, x_pos],
  },
  { intros h,
    by_contradiction H,
    cases h with x h,
    cases h with x_pos h,
    exact h (H x x_pos),
  },
end

end negation_quantifiers

