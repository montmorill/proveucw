import Proveucw

section Chapter1

theorem Prop1_1 : Beatable {⟦0 ~~ 1 ~~ 2 ~~ ω⟧} := by
  apply Axiom1 (0 ~~ 1 ~~ 2 ~~ ω)
  all_goals decide

theorem Prop1_2 : Beatable {⟦2 ~~ 1 ~~ 0 ~~ ω ~~ 3⟧} := by
  have h : Beatable {⟦2 ~~ 1 ~~ 0 ~~ ω ~~ 3⟧, ⟦0 ~~ ω⟧} := by
    apply Rule1_1 (2 ~~ 1 ~~ 0 ~~ ω ~~ 3)
    apply Axiom1 (0 ~~ ω)
    all_goals decide
  apply Rule1_2 (0 ~~ ω) (2 ~~ 1 ~~ 0 ~~ ω ~~ 3)


-- theorem Prop1_3 : Beatable (lv [(0 ~~ 1 ~~ 2), (1 ~~ 2 ~~ ω)] ∅) := by
--   have h : Beatable (lv [(0 ~~ 1 ~~ 2), (0 ~~ 1 ~~ 2 ~~ ω)] ∅) := by
--     convert Rule1_1 _ Prop1_1 (0 ~~ 1 ~~ 2)
--   have h2 : Beatable (lv [(0 ~~ 1 ~~ 2), (0 ~~ 1), (1 ~~ 2 ~~ ω)] ∅) := by
--     convert Rule1_3 _ h (0 ~~ 1) (1 ~~ 2 ~~ ω) (by decide) (by decide)
--     decide
--   convert Rule1_2 _ h2 (0 ~~ 1) (0 ~~ 1 ~~ 2) (by decide) (by decide)

-- theorem Prop1_4 : Beatable (lv [(2 ~~ 6 ~~ 2), (0 ~~ 1 ~~ 2 ~~ 3), (4 ~~ 5 ~~ 6 ~~ 7 ~~ ω)] ∅) := by
--   suffices Beatable (lv [(2 ~~ 6), (0 ~~ 1 ~~ 2 ~~ 3), (4 ~~ 5 ~~ 6 ~~ 7 ~~ ω)] ∅) by
--     obtain h := Rule1_1 _ this (2 ~~ 6 ~~ 2)
--     convert Rule1_2 _ h (2 ~~ 6) (2 ~~ 6 ~~ 2) (by decide) (by decide)
--   suffices Beatable (lv [(2 ~~ 6), (0 ~~ 1 ~~ 2), (4 ~~ 5 ~~ 6 ~~ 7 ~~ ω)] ∅) by
--     obtain h := Rule1_1 _ this (0 ~~ 1 ~~ 2 ~~ 3)
--     convert Rule1_2 _ h (0 ~~ 1 ~~ 2) (0 ~~ 1 ~~ 2 ~~ 3) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(2 ~~ 6), (0 ~~ 1 ~~ 2), (6 ~~ 7 ~~ ω)] ∅) by
--     obtain h := Rule1_1 _ this (4 ~~ 5 ~~ 6 ~~ 7 ~~ ω)
--     convert Rule1_2 _ h (6 ~~ 7 ~~ ω) (4 ~~ 5 ~~ 6 ~~ 7 ~~ ω) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 6), (6 ~~ 7 ~~ ω)] ∅) by
--     convert Rule1_3 _ this (0 ~~ 1 ~~ 2) (2 ~~ 6) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 6 ~~ 7 ~~ ω)] ∅) by
--     convert Rule1_3 _ this (0 ~~ 1 ~~ 2 ~~ 6) (6 ~~ 7 ~~ ω) (by decide) (by decide)
--   apply Lemma1 _ (0 ~~ 1 ~~ 2 ~~ 6 ~~ 7 ~~ ω)
--   all_goals decide

-- /--!
-- Chapter 2
-- -/

-- theorem Prop2_1 : Beatable (lv [(1 ~~ 2), (0 ~~ 1 ~L(0)~ 2 ~~ ω)] ∅) := by
--   suffices Beatable (lv [(1 ~~ 2), (0 ~~ 1 ~L(0)~ 2 ~~ ω), (0 ~~ 1)] ∅) by
--     convert Rule1_2 _ this (0 ~~ 1) (0 ~~ 1 ~L(0)~ 2 ~~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(1 ~~ 2), (0 ~~ 1 ~L(0)~ 2 ~~ ω), (0 ~~ 1), (2 ~~ ω)] ∅) by
--     convert Rule1_2 _ this (2 ~~ ω) (0 ~~ 1 ~L(0)~ 2 ~~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2), (0 ~~ 1 ~L(0)~ 2 ~~ ω), (2 ~~ ω)] ∅) by
--     convert Rule1_3 _ this (0 ~~ 1) (1 ~~ 2) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ ω), (0 ~~ 1 ~L(0)~ 2 ~~ ω)] ∅) by
--     convert Rule1_3 _ this (0 ~~ 1 ~~ 2) (2 ~~ ω) (by decide) (by decide)
--     decide
--   apply Lemma1 _ (0 ~~ 1 ~~ 2 ~~ ω)
--   all_goals decide

-- theorem Prop2_2 : Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω)] <| im [(2, [K(0)])]) := by
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2)] <| im [(2, [K(0)])]) by
--     convert Rule1_2 _ this (0 ~~ 1 ~~ 2) (0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω) (by decide) (by decide)
--   have h : Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 3 ~~ ω), (0 ~~ 1 ~~ 2)] <| im [(2, [K(0)])]) := by
--     apply Lemma1 _ (0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)
--     all_goals decide
--   convert Rule2_1 _ h (0 ~~ 1 ~~ 2) (0 ~~ 1 ~~ 2 ~~ 3 ~~ ω) 0 3 (by decide) (by decide)
--     (by decide) (by decide) (by decide)

-- theorem Prop2_3 : Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω)] <| im [(4, [K(0)])]) := by
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω)] <| im [(4, [K(0)])]) by
--     obtain h := Rule1_3 _ this (0 ~~ 1 ~~ 2) (2 ~~ 4) (by decide) (by decide)
--     convert Rule1_2 _ h (0 ~~ 1 ~~ 2) (0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 4), (0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω)] <| im [(4, [K(0)])]) by
--     convert Rule2_1 _ this (0 ~~ 1 ~~ 2 ~~ 4) (0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω) 0 2
--       (by decide) (by decide) (by decide) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 4), (0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)] <| im [(4, [K(0)])]) by
--     convert Rule2_1 _ this (0 ~~ 1 ~~ 2 ~~ 4) (0 ~~ 1 ~~ 2 ~~ 3 ~~ ω) 0 3
--       (by decide) (by decide) (by decide) (by decide) (by decide)
--     decide
--   apply Lemma1 _ (0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)
--   all_goals decide

-- theorem Prop2_4 :
--     Beatable (lv [(2 ~~ 4 ~L(1)~ 5), (0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω)] <| im [(3, [K(1)]), (5, [K(0)])]) := by

--   suffices Beatable (lv [(2 ~~ 4 ~L(1)~ 5), (0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2 ~~ 3)]
--       <| im [(3, [K(1)]), (5, [K(0)])]) by
--     convert Rule1_2 _ this (0 ~~ 1 ~~ 2 ~~ 3) (0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(2 ~~ 4 ~~ 5), (0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2 ~~ 3)]
--       <| im [(3, [K(1)]), (5, [K(0)])]) by
--     convert Rule2_1 _ this (0 ~~ 1 ~~ 2 ~~ 3) (2 ~~ 4 ~~ 5) 1 1
--       (by decide) (by decide) (by decide) (by decide) (by decide)
--   suffices Beatable (lv [(2 ~~ 4 ~~ 5), (0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2 ~~ 3), (0 ~~ 1 ~~ 2)]
--       <| im [(3, [K(1)]), (5, [K(0)])]) by
--     convert Rule1_2 _ this (0 ~~ 1 ~~ 2) (0 ~~ 1 ~~ 2 ~~ 3) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2 ~~ 3), (0 ~~ 1 ~~ 2 ~~ 4 ~~ 5)]
--       <| im [(3, [K(1)]), (5, [K(0)])]) by
--     convert Rule1_3 _ this (0 ~~ 1 ~~ 2) (2 ~~ 4 ~~ 5) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ 3 ~~ ω), (0 ~~ 1 ~~ 2 ~~ 3), (0 ~~ 1 ~~ 2 ~~ 4 ~~ 5)]
--       <| im [(3, [K(1)]), (5, [K(0)])]) by
--     convert Rule2_1 _ this (0 ~~ 1 ~~ 2 ~~ 4 ~~ 5) (0 ~~ 1 ~~ 2 ~~ 3 ~~ ω) 0 3
--       (by decide) (by decide) (by decide) (by decide) (by decide)
--   apply Lemma1 _ (0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)
--   all_goals decide

-- theorem Prop2_5 :
--     Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω)] <| im [(2, [K*(0), K*(0)])]) := by

--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2)]
--       <| im [(2, [K*(0), K*(0)])]) by
--     convert Rule1_2 _ this (0 ~~ 1 ~~ 2) (0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2), (2 ~L(0)~ 3)]
--       <| im [(2, [K*(0), K*(0)])]) by
--     convert Rule1_2 _ this (2 ~L(0)~ 3) (0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2), (2 ~L(0)~ 3), (3 ~L(0)~ ω)]
--       <| im [(2, [K*(0), K*(0)])]) by
--     convert Rule1_2 _ this (3 ~L(0)~ ω) (0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2), (2 ~~ 3), (3 ~L(0)~ ω)]
--       <| im [(2, [K*(0)])]) by
--     convert Rule2_3 _ this (0 ~~ 1 ~~ 2) (2 ~~ 3) 0 (by decide) (by decide) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2), (2 ~~ 3), (3 ~L(0)~ ω)]
--       <| im [(3, [K*(0)])]) by
--     convert Rule2_2 _ this (3 ~~ 2) 0 (by decide) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2 ~~ 3), (3 ~L(0)~ ω)]
--       <| im [(3, [K*(0)])]) by
--     convert Rule1_3 _ this (0 ~~ 1 ~~ 2) (2 ~~ 3) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2 ~~ 3), (3 ~~ ω)] ∅) by
--     convert Rule2_3 _ this (0 ~~ 1 ~~ 2 ~~ 3) (3 ~~ ω) 0 (by decide) (by decide) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ 3 ~L(0)~ ω), (0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)] ∅) by
--     convert Rule1_3 _ this (0 ~~ 1 ~~ 2 ~~ 3) (3 ~~ ω) (by decide) (by decide)
--     decide
--   apply Lemma1 _ (0 ~~ 1 ~~ 2 ~~ 3 ~~ ω)
--   all_goals decide

-- theorem Prop2_6 :
--     Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω)] <| im [(4, [K*(0)])]) := by
--   suffices Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (0 ~~ 1 ~~ 2)] <| im [(4, [K*(0)])]) by
--     convert Rule1_2 _ this (0 ~~ 1 ~~ 2) (0 ~~ 1 ~~ 2 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (0 ~~ 1 ~~ 2), (2 ~L(0)~ ω)] <| im [(4, [K*(0)])]) by
--     convert Rule1_2 _ this (2 ~L(0)~ ω) (0 ~~ 1 ~~ 2 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (0 ~~ 1 ~~ 2), (2 ~L(0)~ ω), (0 ~~ 1 ~~ 2)]
--       <| im [(4, [K*(0)])]) by
--     convert Rule1_2 _ this (0 ~~ 1 ~~ 2) (0 ~~ 1 ~~ 2) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (0 ~~ 1 ~~ 2), (2 ~L(0)~ ω), (0 ~~ 1 ~~ 2)]
--       <| im [(2, [K*(0)])]) by
--     convert Rule2_2 _ this (2 ~~ 4) 0 (by decide) (by decide) (by decide)
--   suffices Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (0 ~~ 1 ~~ 2), (2 ~~ ω), (0 ~~ 1 ~~ 2)] ∅) by
--     convert Rule2_3 _ this (0 ~~ 1 ~~ 2) (2 ~~ ω) 0 (by decide) (by decide) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (0 ~~ 1 ~~ 2 ~~ ω), (0 ~~ 1 ~~ 2)] ∅) by
--     convert Rule1_3 _ this (0 ~~ 1 ~~ 2) (2 ~~ ω) (by decide) (by decide)
--     decide
--   apply Lemma1 _ (0 ~~ 1 ~~ 2 ~~ ω)
--   all_goals decide

-- theorem Prop2_7 :
--     Beatable (lv [(2 ~L(1)~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω)] <| im [(1, [K*(1)]), (4, [K*(0)])]) := by
--   suffices Beatable (lv [(2 ~L(1)~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (1 ~~ 2)]
--       <| im [(1, [K*(1)]), (4, [K*(0)])]) by
--     convert Rule1_2 _ this (1 ~~ 2) (0 ~~ 1 ~~ 2 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(2 ~L(1)~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (1 ~~ 2)]
--       <| im [(2, [K*(1)]), (4, [K*(0)])]) by
--     convert Rule2_2 _ this (2 ~~ 1) 1 (by decide) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(2 ~L(1)~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (1 ~~ 2), (0 ~~ 1 ~~ 2)]
--       <| im [(2, [K*(1)]), (4, [K*(0)])]) by
--     convert Rule1_2 _ this (0 ~~ 1 ~~ 2) (0 ~~ 1 ~~ 2 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (1 ~~ 2), (0 ~~ 1 ~~ 2)]
--       <| im [(4, [K*(0)])]) by
--     convert Rule2_3 _ this (0 ~~ 1 ~~ 2) (2 ~~ 4) 1 (by decide) (by decide) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω), (1 ~~ 2)]
--       <| im [(4, [K*(0)])]) by
--     convert Rule1_1 _ this (0 ~~ 1 ~~ 2)
--     decide
--   suffices Beatable (lv [(2 ~~ 4), (0 ~~ 1 ~~ 2 ~L(0)~ ω)]
--       <| im [(4, [K*(0)])]) by
--     convert Rule1_1 _ this (1 ~~ 2)
--     decide
--   exact Prop2_6

-- theorem Prop2_8 :  -- second prop
--     Beatable (lv [(1 ~L(0)~ 4), (0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω)] <| im [(1, [K*(0)]), (4, [K(0)])]) := by
--   suffices Beatable (lv [(1 ~L(0)~ 4), (0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω), (0 ~~ 1)] <| im [(1, [K*(0)]), (4, [K(0)])]) by
--     convert Rule1_2 _ this (0 ~~ 1) (0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(1 ~~ 4), (0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω), (0 ~~ 1)] <| im [(4, [K(0)])]) by
--     convert Rule2_3 _ this (0 ~~ 1) (1 ~~ 4) 0 (by decide) (by decide) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~L(0)~ 2 ~L(0)~ ω), (0 ~~ 1 ~~ 4)] <| im [(4, [K(0)])]) by
--     convert Rule1_3 _ this (0 ~~ 1) (1 ~~ 4) (by decide) (by decide)
--     decide
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~L(0)~ ω), (0 ~~ 1 ~~ 4)] <| im [(4, [K(0)])]) by
--     convert Rule2_1 _ this (0 ~~ 1 ~~ 4) (0 ~~ 1 ~~ 2 ~L(0)~ ω) 0 1
--       (by decide) (by decide) (by decide) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 1 ~~ 2 ~~ ω), (0 ~~ 1 ~~ 4)] <| im [(4, [K(0)])]) by
--     convert Rule2_1 _ this (0 ~~ 1 ~~ 4) (0 ~~ 1 ~~ 2 ~~ ω) 0 2
--       (by decide) (by decide) (by decide) (by decide) (by decide)
--   apply Lemma1 _ (0 ~~ 1 ~~ 2 ~~ ω)
--   all_goals decide

-- /--!
-- Chapter 3
-- -/

-- theorem Prop3_1 : ¬ Beatable (lv [(1 ~~ 2), (3 ~~ 4)] ∅) := by
--   apply Axiom2 (1 ~~ 2) (3 ~~ 4) _
--   all_goals decide

-- theorem Prop3_2 : ¬ Beatable (lv [(0 ~~ 1 ~~ 2), (3 ~~ 4 ~L(0)~ ω)] <| im [(2, [K(0)])]) := by
--   apply Axiom2 (0 ~~ 1 ~~ 2) (3 ~~ 4 ~L(0)~ ω) _
--   all_goals decide

-- theorem Prop3_3 : ¬ Beatable (lv [] ∅) := by
--   obtain h := Axiom2 (100) (12345) ∅ (by decide) (by decide) (by decide)
--   contrapose! h with h1
--   obtain h2 := Rule1_1 _ h1 (100)
--   convert Rule1_1 _ h2 (12345)
--   decide

-- theorem Prop3_4 : ¬ Beatable (lv [(4 ~~ ω), (6 ~~ 5 ~~ 7), (0 ~~ 1 ~~ 2 ~~ 3)] ∅) := by
--   by_contra! h1
--   have h2 : Beatable (lv [(4 ~~ ω), (6 ~~ 5 ~~ 7), (0 ~~ 1 ~~ 2 ~~ 3), (0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)] ∅) := by
--     convert Rule1_1 _ h1 (0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)
--     decide
--   have h3 : Beatable (lv [(4 ~~ ω), (0 ~~ 1 ~~ 2 ~~ 3), (0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)] ∅) := by
--     convert Rule1_2 _ h2 (6 ~~ 5 ~~ 7) (0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7) (by decide) (by decide)
--   have h4 : Beatable (lv [(4 ~~ ω), (0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)] ∅) := by
--     convert Rule1_2 _ h3 (0 ~~ 1 ~~ 2 ~~ 3) (0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7) (by decide) (by decide)
--   have h : ¬ Beatable (lv [(4 ~~ ω), (0 ~~ 1 ~~ 2 ~~ 3 ~~ 6 ~~ 5 ~~ 7)] ∅) :=
--     Axiom2 _ _ _ (by decide) (by decide) (by decide)
--   contradiction

-- theorem Prop3_5 : ¬ Beatable (lv [(5 ~~ 6), (7 ~~ ω), (0 ~~ 2 ~~ 3), (1 ~~ 2 ~~ 4)] ∅) := by
--   obtain h := Axiom2 (5 ~~ 6 ~~ 7 ~~ ω) (0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4) ∅ (by decide) (by decide) (by decide)
--   contrapose! h with h1
--   suffices Beatable (lv [(5 ~~ 6 ~~ 7 ~~ ω), (0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), (5 ~~ 6)] ∅) by
--     convert Rule1_2 _ this (5 ~~ 6) (5 ~~ 6 ~~ 7 ~~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(5 ~~ 6 ~~ 7 ~~ ω), (0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), (5 ~~ 6), (7 ~~ ω)] ∅) by
--     convert Rule1_2 _ this (7 ~~ ω) (5 ~~ 6 ~~ 7 ~~ ω) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), (5 ~~ 6), (7 ~~ ω)] ∅) by
--     convert Rule1_1 _ this (5 ~~ 6 ~~ 7 ~~ ω)
--   suffices Beatable (lv [(0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), (5 ~~ 6), (7 ~~ ω), (0 ~~ 2 ~~ 3)] ∅) by
--     convert Rule1_2 _ this (0 ~~ 2 ~~ 3) (0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4) (by decide) (by decide)
--   suffices Beatable (lv [(0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4), (5 ~~ 6), (7 ~~ ω), (0 ~~ 2 ~~ 3), (1 ~~ 2 ~~ 4)] ∅) by
--     convert Rule1_2 _ this (1 ~~ 2 ~~ 4) (0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4) (by decide) (by decide)
--   suffices Beatable (lv [(5 ~~ 6), (7 ~~ ω), (0 ~~ 2 ~~ 3), (1 ~~ 2 ~~ 4)] ∅) by
--     convert Rule1_1 _ this (0 ~~ 2 ~~ 3 ~~ 1 ~~ 2 ~~ 4)
--   exact h1

-- theorem Prop3_6 : ¬ Beatable (lv [(0 ~~ 1 ~L(0)~ 2 ~~ ω)] <| im [(2, [K(0)])]) := by
--   suffices ¬ Beatable (lv [(0 ~~ 1 ~L(0)~ 2), (2 ~~ ω)] <| im [(2, [K(0)])]) by
--     contrapose! this
--     convert Rule1_3 _ this (0 ~~ 1 ~L(0)~ 2) (2 ~~ ω) (by decide) (by decide)
--   suffices ¬ Beatable (lv [(0 ~~ 1 ~L(0)~ 2), (2 ~~ ω)] ∅) by
--     convert Rule3_3 _ this (2 ~~ ω) (K(0)) (by decide)
--   suffices ¬ Beatable (lv [(0 ~~ 1), (1 ~L(0)~ 2), (2 ~~ ω)] ∅) by
--     contrapose! this
--     convert Rule1_3 _ this (0 ~~ 1) (1 ~L(0)~ 2) (by decide) (by decide)
--   suffices ¬ Beatable (lv [(0 ~~ 1), (2 ~~ ω)] ∅) by
--     convert Rule3_2 _ this 0 1 2 (by decide)
--     decide
--   apply Axiom2 (0 ~~ 1) (2 ~~ ω)
--   all_goals decide

-- theorem Prop3_7 : ¬ Beatable (lv [(0 ~L(0)~ 1 ~~ ω), (0 ~L(1)~ 2 ~~ ω)]
--     <| im [(1, [K(1)]), (2, [K(0)])]) := by
--   suffices ¬ Beatable (lv [(0 ~L(0)~ 1), (1 ~~ ω), (0 ~L(1)~ 2 ~~ ω)]
--       <| im [(1, [K(1)]), (2, [K(0)])]) by
--     contrapose! this
--     convert Rule1_3 _ this (0 ~L(0)~ 1) (1 ~~ ω) (by decide) (by decide)
--   suffices ¬ Beatable (lv [(0 ~L(0)~ 1), (1 ~~ ω), (0 ~L(1)~ 2), (2 ~~ ω)]
--       <| im [(1, [K(1)]), (2, [K(0)])]) by
--     contrapose! this
--     convert Rule1_3 _ this (0 ~L(1)~ 2) (2 ~~ ω) (by decide) (by decide)
--     decide
--   suffices ¬ Beatable (lv [(0 ~L(0)~ 1), (1 ~~ ω), (0 ~L(1)~ 2), (2 ~~ ω)]
--       <| im [(2, [K(0)])]) by
--     convert Rule3_3 _ this (1 ~~ ω) (K(1)) (by decide)
--     decide
--   suffices ¬ Beatable (lv [(0 ~L(0)~ 1), (1 ~~ ω), (0 ~L(1)~ 2), (2 ~~ ω)] ∅) by
--     convert Rule3_3 _ this (2 ~~ ω) (K(0)) (by decide)
--   suffices ¬ Beatable (lv [(1 ~~ ω), (0 ~L(1)~ 2), (2 ~~ ω)] ∅) by
--     convert Rule3_2 _ this 0 1 0 (by decide)
--     decide
--   suffices ¬ Beatable (lv [(1 ~~ ω), (2 ~~ ω)] ∅) by
--     convert Rule3_2 _ this 1 0 2 (by decide)
--     decide
--   suffices ¬ Beatable (lv [(1 ~~ ω), (2 ~~ ω), (1 ~~ ω ~~ 2)] ∅) by
--     contrapose! this
--     convert Rule1_1 _ this (1 ~~ ω ~~ 2)
--     decide
--   suffices ¬ Beatable (lv [(2 ~~ ω), (1 ~~ ω ~~ 2)] ∅) by
--     contrapose! this
--     convert Rule1_2 _ this (1 ~~ ω) (1 ~~ ω ~~ 2) (by decide) (by decide)
--   suffices ¬ Beatable (lv [(1 ~~ ω ~~ 2)] ∅) by
--     contrapose! this
--     convert Rule1_2 _ this (2 ~~ ω) (1 ~~ ω ~~ 2) (by decide) (by decide)
--   suffices ¬ Beatable (lv [(0), (1 ~~ ω ~~ 2)] ∅) by
--     contrapose! this
--     convert Rule1_1 _ this (0)
--   apply Axiom2 (0) (1 ~~ ω ~~ 2) ∅
--   all_goals decide

-- theorem Prop3_8 : ¬ Beatable (lv [(0 ~L(0)~ 1), (0 ~L(0)~ ω), (0 ~L(1)~ 2), (0 ~L(1)~ ω)]
--     <| im [(1, [K(1)]), (2, [K(0)])]) := by
--   suffices ¬ Beatable (lv [(1 ~~ ω), (0 ~L(0)~ 1), (0 ~L(0)~ ω), (0 ~L(1)~ 2), (0 ~L(1)~ ω)]
--       <| im [(1, [K(1)]), (2, [K(0)])]) by
--     contrapose! this
--     convert Rule1_1 _ this (1 ~~ ω)
--   suffices ¬ Beatable (lv [(1 ~~ ω), (0 ~L(0)~ 1), (0 ~L(0)~ ω), (0 ~L(1)~ 2), (0 ~L(1)~ ω)]
--       <| im [(2, [K(0)])]) by
--     convert Rule3_3 _ this (1 ~~ ω) (K(1)) (by decide)
--     decide
--   suffices ¬ Beatable (lv [(2 ~~ ω), (1 ~~ ω), (0 ~L(0)~ 1),
--       (0 ~L(0)~ ω), (0 ~L(1)~ 2), (0 ~L(1)~ ω)]
--       <| im [(2, [K(0)])]) by
--     contrapose! this
--     convert Rule1_1 _ this (2 ~~ ω)
--   suffices ¬ Beatable (lv [(2 ~~ ω), (1 ~~ ω), (0 ~L(0)~ 1),
--       (0 ~L(0)~ ω), (0 ~L(1)~ 2), (0 ~L(1)~ ω)] ∅) by
--     convert Rule3_3 _ this (2 ~~ ω) (K(0)) (by decide)
--   suffices ¬ Beatable (lv [(2 ~~ ω), (1 ~~ ω)] ∅) by
--     obtain h1 := Rule3_2 _ this 0 0 1 (by decide)
--     obtain h2 := Rule3_2 _ h1 0 0 ω (by decide)
--     obtain h3 := Rule3_2 _ h2 1 0 2 (by decide)
--     convert Rule3_2 _ h3 1 0 ω (by decide)
--     decide
--   suffices ¬ Beatable (lv [(2 ~~ ω), (1 ~~ ω), (2 ~~ ω ~~ 1)] ∅) by
--     contrapose! this
--     convert Rule1_1 _ this (2 ~~ ω ~~ 1)
--     decide
--   suffices ¬ Beatable (lv [(1 ~~ ω), (2 ~~ ω ~~ 1)] ∅) by
--     contrapose! this
--     convert Rule1_2 _ this (2 ~~ ω) (2 ~~ ω ~~ 1) (by decide) (by decide)
--   suffices ¬ Beatable (lv [(2 ~~ ω ~~ 1)] ∅) by
--     contrapose! this
--     convert Rule1_2 _ this (1 ~~ ω) (2 ~~ ω ~~ 1) (by decide) (by decide)
--   suffices ¬ Beatable (lv [(0), (2 ~~ ω ~~ 1)] ∅) by
--     contrapose! this
--     convert Rule1_1 _ this (0)
--   apply Axiom2 (0) (2 ~~ ω ~~ 1) ∅
--   all_goals decide

-- theorem Prop3_9 : ¬ Beatable (lv [(0 ~L(0)~ 1 ~L(0)~ ω)] <| im [(1, [K*(0)])]) := by
--   suffices ¬ Beatable (lv [(0 ~L(0)~ 1 ~L(0)~ ω), (1 ~~ ω)] <| im [(1, [K*(0)])]) by
--     contrapose! this
--     convert Rule1_1 _ this (1 ~~ ω)
--     decide
--   suffices ¬ Beatable (lv [(0 ~L(0)~ 1 ~L(0)~ ω), (1 ~~ ω)] ∅) by
--     convert Rule3_3 _ this (1 ~~ ω) (K*(0)) (by decide)
--   suffices ¬ Beatable (lv [(0 ~L(0)~ 1), (1 ~L(0)~ ω), (1 ~~ ω)] ∅) by
--     contrapose! this
--     convert Rule1_3 _ this (0 ~L(0)~ 1) (1 ~L(0)~ ω) (by decide) (by decide)
--   suffices ¬ Beatable (lv [(1 ~L(0)~ ω), (1 ~~ ω)] ∅) by
--     convert Rule3_2 _ this 0 0 1 (by decide)
--   suffices ¬ Beatable (lv [(1 ~~ ω)] ∅) by
--     convert Rule3_2 _ this 0 1 ω (by decide)
--   suffices ¬ Beatable (lv [(1 ~~ ω), (2)] ∅) by
--     contrapose! this
--     convert Rule1_1 _ this (2)
--     decide
--   apply Axiom2 (1 ~~ ω) (2) ∅
--   all_goals decide
