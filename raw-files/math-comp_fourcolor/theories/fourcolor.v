
From fourcolor
Require Import real realplane.
From fourcolor
Require combinatorial4ct discretize finitize.

Section FourColorTheorem.

Variable Rmodel : Real.model.
Let R := Real.model_structure Rmodel.
Implicit Type m : map R.

Theorem four_color_finite m : finite_simple_map m -> colorable_with 4 m.
Proof.
intros fin_m.
pose proof (discretize.discretize_to_hypermap fin_m) as [G planarG colG].
exact (colG (combinatorial4ct.four_color_hypermap planarG)).
Qed.

Theorem four_color m : simple_map m -> colorable_with 4 m.
Proof. revert m; exact (finitize.compactness_extension four_color_finite). Qed.

End FourColorTheorem.