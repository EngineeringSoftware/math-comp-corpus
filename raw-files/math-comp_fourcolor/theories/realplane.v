
From fourcolor
Require Import real.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Definitions.

Variable R : Real.structure.

Inductive point : Type := Point (x y : Real.val R).

Definition region : Type := point -> Prop.

Definition map : Type := point -> region.

Inductive interval : Type := Interval (x y : Real.val R).

Inductive rectangle : Type := Rectangle (hspan vspan : interval).

Definition in_interval (s : interval) : Real.set R :=
  fun t => let ' Interval x y := s in Real.lt x t /\ Real.lt t y.

Definition in_rectangle rr : region :=
  fun z => let ' Rectangle hspan vspan := rr in let ' Point x y := z in
  in_interval hspan x /\ in_interval vspan y.

Definition union (r1 r2 : region) : region := fun z => r1 z \/ r2 z.

Definition intersect (r1 r2 : region) : region := fun z => r1 z /\ r2 z.

Definition nonempty (r : region) : Prop := exists z : point, r z.

Definition subregion (r1 r2 : region) : Prop := forall z : point, r1 z -> r2 z.

Definition meet (r1 r2 : region) : Prop := nonempty (intersect r1 r2).

Record plain_map (m : map) : Prop := PlainMap {
  map_sym z1 z2 : m z1 z2 -> m z2 z1;
  map_trans z1 z2 : m z1 z2 -> subregion (m z2) (m z1)
}.

Definition cover (m : map) : region := fun z => m z z.

Definition submap (m1 m2 : map) : Prop := forall z, subregion (m1 z) (m2 z).

Definition at_most_regions (n : nat) (m : map) :=
  exists f, forall z, cover m z -> exists2 i : nat, Peano.lt i n & m (f i) z.

Definition open (r : region) : Prop :=
  forall z, r z -> exists2 u, in_rectangle u z & subregion (in_rectangle u) r.

Definition closure (r : region) : region :=
  fun z => forall u, open u -> u z -> meet r u.

Definition connected (r : region) : Prop :=
  forall u v, open u -> open v -> subregion r (union u v) ->
  meet u r -> meet v r -> meet u v.

Record simple_map (m : map) : Prop := SimpleMap {
  simple_map_plain : plain_map m;
  simple_map_open z : open (m z);
  simple_map_connected z : connected (m z)
}.

Record finite_simple_map (m : map) : Prop := FiniteSimpleMap {
  finite_simple_map_simple : simple_map m;
  finite_simple_map_finite : exists n, at_most_regions n m
}.

Definition border (m : map) (z1 z2 : point) : region :=
  intersect (closure (m z1)) (closure (m z2)).

Definition corner_map (m : map) (z : point) : map :=
  fun z1 z2 => m z1 z2 /\ closure (m z1) z.

Definition not_corner (m : map) : region :=
  fun z => at_most_regions 2 (corner_map m z).

Definition adjacent (m : map) (z1 z2 : point) : Prop :=
  ~ m z1 z2 /\ meet (not_corner m) (border m z1 z2).

Record coloring (m k : map) : Prop := Coloring {
  coloring_plain : plain_map k;
  coloring_cover : subregion (cover k) (cover m);
  coloring_consistent : submap m k;
  coloring_adjacent z1 z2 : adjacent m z1 z2 -> ~ k z1 z2
}.

Definition colorable_with (n : nat) (m : map) : Prop :=
  exists2 k, coloring m k & at_most_regions n k.

End Definitions.

Module RealPlaneCoercions.

Identity Coercion in_region : region >-> Funclass.
Identity Coercion in_map : map >-> Funclass.
Coercion in_interval : interval >-> Real.set.
Coercion in_rectangle : rectangle >-> region.
Coercion simple_map_plain : simple_map >-> plain_map.
Coercion finite_simple_map_simple : finite_simple_map >-> simple_map.
Coercion coloring_plain : coloring >-> plain_map.

End RealPlaneCoercions.