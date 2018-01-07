Require Semantics Tableau.

Extraction Language Haskell.

Extract Inductive list => "([])" [ "[]" "(:)" ].
Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"] "(\ f0 fs x -> if (Prelude.==) x 0 then f0 () else fs ((Prelude.-) x 1))".
Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

Extraction "NNFTableau.hs" Tableau.tableau_list.