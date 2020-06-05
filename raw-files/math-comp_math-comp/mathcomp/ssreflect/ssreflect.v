
From Coq Require Export ssreflect.
Global Set SsrOldRewriteGoalsOrder.
Global Set Asymmetric Patterns.
Global Set Bullet Behavior "None".

Module NonPropType.

Structure call_of (condition : unit) (result : bool) := Call {callee : Type}.
Definition maybeProp (T : Type) := tt.
Definition call T := Call (maybeProp T) false T.

Structure test_of (result : bool) := Test {condition :> unit}.
Definition test_Prop (P : Prop) := Test true (maybeProp P).
Definition test_negative := Test false tt.

Structure type :=
  Check {result : bool; test : test_of result; frame : call_of test result}.
Definition check result test frame := @Check result test frame.

Module Exports.
Canonical call.
Canonical test_Prop.
Canonical test_negative.
Canonical check.
Notation nonPropType := type.
Coercion callee : call_of >-> Sortclass.
Coercion frame : type >-> call_of.
Notation notProp T := (@check false test_negative (call T)).
End Exports.

End NonPropType.
Export NonPropType.Exports.

Module Deprecation.

Definition hidden (T : Type) := T.
Definition exposed (T : Type) & unit -> unit -> unit := T.
Definition hide T u (v : exposed T u) : hidden T := v.

Ltac warn old_id new_id :=
  idtac "Warning:" old_id "is deprecated; use" new_id "instead".

Ltac stop old_id new_id :=
  fail 1 "Error:" old_id "is deprecated; use" new_id "instead".

Structure hinted := Hint {statement; hint : statement}.
Ltac check cond := let test := constr:(hint _ : cond) in idtac.

Variant reject := Reject.
Definition reject_hint := Hint reject Reject.
Module Reject. Canonical reject_hint. End Reject.

Variant silent := Silent.
Definition silent_hint := Hint silent Silent.
Module Silent. Canonical silent_hint. End Silent.

Ltac flag old_id new_id :=
  first [check reject; stop old_id new_id | check silent | warn old_id new_id].

Module Exports.
Arguments hide {T} u v /.
Coercion hide : exposed >-> hidden.
Notation deprecate old_id new_id :=
  (hide (fun old_id new_id => ltac:(flag old_id new_id; exact tt)) new_id)
  (only parsing).
End Exports.

End Deprecation.
Export Deprecation.Exports.