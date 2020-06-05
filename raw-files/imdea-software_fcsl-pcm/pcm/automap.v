

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq.
From fcsl Require Import pred ordtype pcm unionmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Helpers.
Variable A : Type.

Fixpoint onth (s : seq A) n : option A :=
  if s is x::sx then if n is nx.+1 then onth sx nx else Some x else None.

Definition prefix s1 s2 :=
  forall n x, onth s1 n = some x -> onth s2 n = some x.

Lemma size_onth s n : n < size s -> exists x, onth s n = Some x.
Proof.
elim: s n=>[//|a s IH] [|n] /=; first by exists a.
by rewrite -(addn1 n) -(addn1 (size s)) ltn_add2r; apply: IH.
Qed.

Lemma onth_size s n x : onth s n = Some x -> n < size s.
Proof. by elim: s n=>[//|a s IH] [//|n]; apply: IH. Qed.

Lemma prefix_refl s : prefix s s.
Proof. by move=>n x <-. Qed.

Lemma prefix_trans s2 s1 s3 : prefix s1 s2 -> prefix s2 s3 -> prefix s1 s3.
Proof. by move=>H1 H2 n x E; apply: H2; apply: H1. Qed.

Lemma prefix_cons x s1 s2 : prefix (x :: s1) (x :: s2) <-> prefix s1 s2.
Proof. by split=>E n; [apply: (E n.+1) | case: n]. Qed.

Lemma prefix_cons' x y s1 s2 :
        prefix (x :: s1) (y :: s2) -> x = y /\ prefix s1 s2.
Proof. by move=>H; case: (H 0 x (erefl _)) (H)=>-> /prefix_cons. Qed.

Lemma prefix_size s1 s2 : prefix s1 s2 -> size s1 <= size s2.
Proof.
elim: s1 s2=>[//|a s1 IH] [|b s2] H; first by move: (H 0 a (erefl _)).
by rewrite ltnS; apply: (IH _ (proj2 (prefix_cons' H))).
Qed.

Lemma prefix_onth s t x : x < size s -> prefix s t -> onth s x = onth t x.
Proof.
elim:s t x =>[//|a s IH] [|b t] x H1 H2; first by move: (H2 0 a (erefl _)).
by case/prefix_cons': H2=><- H2; case: x H1=>[|n] //= H1; apply: IH.
Qed.

End Helpers.

Hint Resolve prefix_refl : core.

Lemma onth_mem (A : eqType) (s : seq A) n x : onth s n = Some x -> x \in s.
Proof.
by elim: s n=>//= a s IH [[->]|n /IH]; rewrite inE ?eq_refl // orbC => ->.
Qed.

Section ReflectionContexts.
Variables (K : ordType) (T : Type) (U : union_map_class K T).

Structure ctx := Context {keyx : seq K; varx : seq U}.

Definition empx := Context [::] [::].

Definition sub_ctx i j := prefix (keyx i) (keyx j) /\ prefix (varx i) (varx j).

Lemma sc_refl i : sub_ctx i i.
Proof. by []. Qed.

Lemma sc_trans i j k : sub_ctx i j -> sub_ctx j k -> sub_ctx i k.
Proof.
by case=>K1 V1 [K2 V2]; split; [move: K2 | move: V2]; apply: prefix_trans.
Qed.

End ReflectionContexts.

Section OneShotFilter.
Variables (A : Type) (p : pred A).

Fixpoint rfilter ts : seq A :=
  if ts is t :: ts' then if p t then ts' else t :: rfilter ts' else [::].
End OneShotFilter.

Section Reflection.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Type i : ctx U.

Inductive term := Pts of nat & T | Var of nat.

Definition interp' i t :=
  match t with
    Pts n v => if onth (keyx i) n is Some k then pts k v else um_undef
  | Var n => if onth (varx i) n is Some f then f else um_undef
  end.

Notation fx i := (fun t f => interp' i t \+ f).
Definition interp i ts := foldr (fx i) Unit ts.

Lemma fE i ts x  : foldr (fx i) x ts = x \+ interp i ts.
Proof. by elim: ts x=>[|t ts IH] x; rewrite /= ?unitR // IH joinCA. Qed.

Lemma interp_rev i ts : interp i (rev ts) = interp i ts.
Proof.
elim: ts=>[|t ts IH] //=; rewrite rev_cons -cats1.
by rewrite /interp foldr_cat fE /= unitR IH.
Qed.

Fixpoint pprint i ts :=
  if ts is t :: ts' then
    if ts' is [::] then interp' i t else interp' i t \+ pprint i ts'
  else Unit.

Lemma pp_interp i ts : pprint i ts = interp i ts.
Proof. by elim: ts=>[|t ts /= <-] //; case: ts=>//; rewrite unitR. Qed.

Definition key n t := if t is Pts m _ then n == m else false.
Definition var n t := if t is Var m then n == m else false.

Definition kfree n t := rfilter (key n) t.
Definition vfree n t := rfilter (var n) t.

Lemma keyN i n ts : ~~ has (key n) ts -> interp i (kfree n ts) = interp i ts.
Proof. by elim: ts=>[|t ts IH] //=; case: ifP=>//= _ /IH ->. Qed.

Lemma varN i n ts : ~~ has (var n) ts -> interp i (vfree n ts) = interp i ts.
Proof. by elim: ts=>[|t ts IH] //=; case: ifP=>//= _ /IH ->. Qed.

Lemma keyP i n k ts :
        has (key n) ts -> onth (keyx i) n = Some k ->
        exists v, interp i ts = pts k v \+ interp i (kfree n ts).
Proof.
elim: ts=>[|t ts IH] //=; case: ifP=>[|_ H].
- by case: t=>//= _ v /eqP <- _ ->; exists v.
by case/(IH H)=>v ->; exists v; rewrite joinCA.
Qed.

Lemma varP i n u ts :
        has (var n) ts -> onth (varx i) n = Some u ->
        interp i ts = u \+ interp i (vfree n ts).
Proof.
elim: ts=>[|t ts IH] //=; case: ifP=>[|_ H].
- by case: t=>//= _ /eqP <- _ ->.
by move/(IH H)=>->; rewrite joinCA.
Qed.

Definition wf i t :=
  match t with
    Pts n _ => n < size (keyx i)
  | Var n => n < size (varx i)
  end.

Lemma sc_wf i j ts : sub_ctx i j -> all (wf i) ts -> all (wf j) ts.
Proof.
case=>/prefix_size H1 /prefix_size H2; elim: ts=>[|t ts IH] //=.
case/andP=>H /IH ->; rewrite andbT.
by case: t H=>[n v|v] H; apply: leq_trans H _.
Qed.

Lemma sc_interp i j ts :
        sub_ctx i j -> all (wf i) ts -> interp i ts = interp j ts.
Proof.
case=>H1 H2; elim: ts=>[|t ts IH] //= /andP [H] /IH ->.
by case: t H=>[n v|n] /= /prefix_onth <-.
Qed.

Lemma valid_wf i ts : valid (interp i ts) -> all (wf i) ts.
Proof.
elim: ts=>[|t ts IH] //= V; rewrite (IH (validR V)) andbT.
case: t {V IH} (validL V)=>[n v|n] /=;
by case X : (onth _ _)=>[a|]; rewrite ?(onth_size X) // valid_undef.
Qed.

Lemma wf_kfree i n ts : all (wf i) ts -> all (wf i) (kfree n ts).
Proof. by elim: ts=>//= t ts IH; case: ifP=>_ /andP [] //= -> /IH ->. Qed.

Lemma wf_vfree i n ts : all (wf i) ts -> all (wf i) (vfree n ts).
Proof. by elim: ts=>//= t ts IH; case: ifP=>_ /andP [] //= -> /IH ->. Qed.

Definition getkeys :=
  foldr (fun t ks => if t is Pts k _ then k :: ks else ks) [::].

Lemma has_getkeys ts n : n \in getkeys ts = has (key n) ts.
Proof. by elim: ts=>//= t ts IH; case: t=>[m v|m] //; rewrite inE IH. Qed.

End Reflection.


Section Subterm.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (i : ctx U) (ts : seq (term T)).

Fixpoint subterm ts1 ts2 :=
  match ts1 with
    Pts n _ :: tsx1 =>
      if has (key n) ts2 then subterm tsx1 (kfree n ts2) else false
  | Var n :: tsx1 =>
      if has (var n) ts2 then subterm tsx1 (vfree n ts2) else false
  | [::] => true
  end.

Lemma subterm_sound i ts1 ts2 :
        all (wf i) ts1 -> all (wf i) ts2 -> subterm ts1 ts2 ->
        exists u, dom_eq (interp i ts1 \+ u) (interp i ts2).
Proof.
elim: ts1 ts2=>[|t ts1 IH] ts2 /= A1 A2.
- by exists (interp i ts2); rewrite unitL.
case/andP: A1; case: t=>[n v|n] /= /size_onth [k] X A1;
rewrite X; case: ifP=>Y //.
- case: (keyP Y X)=>w -> /(IH _ A1 (wf_kfree n A2)) [xs D].
  by exists xs; rewrite -joinA; apply: domeqUn D.
move: (varP Y X)=>-> /(IH _ A1 (wf_vfree n A2)) [xs D].
by exists xs; rewrite -joinA; apply: domeqUn D.
Qed.

End Subterm.

Section Subtract.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (i : ctx U) (ts : seq (term T)).

Fixpoint subtract ts1 ts2 xs :=
  match ts1 with
    Pts n v :: tsx1 =>
      if has (key n) ts2 then subtract tsx1 (kfree n ts2) xs
      else subtract tsx1 ts2 (Pts n v :: xs)
  | Var n :: tsx1 =>
      if has (var n) ts2 then subtract tsx1 (vfree n ts2) xs
      else subtract tsx1 ts2 (Var T n :: xs)
  | [::] => (xs, ts2)
  end.

Lemma subtract_sound i ts1 ts2 rs1 rs2 xs :
        all (wf i) ts1 -> all (wf i) ts2 ->
        subtract ts1 ts2 xs = (rs1, rs2) ->
        exists u, dom_eq (interp i ts1 \+ interp i xs) (interp i rs1 \+ u) /\
                  dom_eq (interp i ts2) (interp i rs2 \+ u).
Proof.
elim: ts1 ts2 xs=>[|t ts1 IH] ts2 xs /= A1 A2.
- by case=><-<-; exists Unit; rewrite unitL !unitR.
case/andP: A1; case: t=>[n v|n] /= /size_onth [x X] A1; rewrite X; case: ifP=>Y.
- case: (keyP Y X)=>w -> /(IH _ _ A1 (wf_kfree n A2)) [u][H1 H2].
  exists (pts x v \+ u); rewrite -joinA !(pull (pts x _)).
  by split=>//; apply: domeqUn.
- by case/(IH _ _ A1 A2)=>u [/= H1 H2]; rewrite X joinCA joinA in H1; exists u.
- move: (varP Y X)=>-> /(IH _ _ A1 (wf_vfree n A2)) [u][H1 H2].
  by exists (x \+ u); rewrite -joinA !(pull x); split=>//; apply: domeqUn.
by case/(IH _ _ A1 A2)=>u [/= H1 H2]; rewrite X joinCA joinA in H1; exists u.
Qed.

End Subtract.

Section Invalid.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (i : ctx U) (t : term T) (ts : seq (term T)).

Definition undefx i t :=
  if t is Var n then
    if onth (varx i) n is Some x then undefb x else false
  else false.

Definition isundef i ts := ~~ uniq (getkeys ts) || has (undefx i) ts.

Lemma isundef_sound i ts :
        all (wf i) ts -> isundef i ts -> ~~ valid (interp i ts).
Proof.
elim: ts=>[|t ts IH] //= /andP [W A].
case: t W=>[n v|n] /= /size_onth [k] X; rewrite /isundef /= X; last first.
- rewrite orbCA=>H; case: validUn=>// V; rewrite (negbTE (IH A _)) //.
  by case/orP: H V=>// /undefbE ->; rewrite valid_undef.
rewrite negb_and negbK has_getkeys -orbA /=.
case/orP=>// V; last by rewrite validPtUn andbCA (negbTE (IH A _)).
by case: (keyP V X)=>u ->; rewrite joinA pts_undef join_undefL valid_undef.
Qed.

End Invalid.


Section XFind.
Variable A : Type.

Structure tagged_elem := XTag {xuntag :> A}.

Definition extend_tag := XTag.
Definition recurse_tag := extend_tag.
Canonical found_tag x := recurse_tag x.

Definition axiom xs1 xs2 i (pivot : tagged_elem) :=
  onth xs2 i = Some (xuntag pivot) /\ prefix xs1 xs2.
Structure xfind (xs1 xs2 : seq A) (i : nat) :=
  Form {pivot :> tagged_elem; _ : axiom xs1 xs2 i pivot}.

Lemma found_pf x t : axiom (x :: t) (x :: t) 0 (found_tag x).
Proof. by []. Qed.
Canonical found_form x t := Form (@found_pf x t).

Lemma recurse_pf i x xs1 xs2 (f : xfind xs1 xs2 i) :
        axiom (x :: xs1) (x :: xs2) i.+1 (recurse_tag (xuntag f)).
Proof. by case: f=>pv [H1 H2]; split=>//; apply/prefix_cons. Qed.
Canonical recurse_form i x xs1 xs2 f := Form (@recurse_pf i x xs1 xs2 f).

Lemma extend_pf x : axiom [::] [:: x] 0 (extend_tag x).
Proof. by []. Qed.
Canonical extend_form x := Form (@extend_pf x).

End XFind.

Module Syntactify.
Section Syntactify.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (i : ctx U) (ts : seq (term T)).

Structure tagged_map := Tag {untag : U}.

Local Coercion untag : tagged_map >-> UMC.sort.

Definition var_tag := Tag.
Definition key_tag := var_tag.
Definition empty_tag := key_tag.
Canonical Structure union_tag hc := empty_tag hc.

Definition axiom i j ts (pivot : tagged_map) :=
  [/\ interp j ts = pivot :> U, sub_ctx i j & all (wf j) ts].
Structure form i j ts := Form {pivot : tagged_map; _ : axiom i j ts pivot}.

Local Coercion pivot : form >-> tagged_map.

Lemma union_pf i j k ts1 ts2 (f1 : form i j ts1) (f2 : form j k ts2) :
        axiom i k (ts1 ++ ts2) (union_tag (untag f1 \+ untag f2)).
Proof.
case: f1 f2=>_ [<- S1 W1][_][<- S2 W2]; split.
- by rewrite /interp foldr_cat fE joinC -(sc_interp S2 W1).
- by apply: sc_trans S1 S2.
by rewrite all_cat (sc_wf S2 W1) W2.
Qed.

Canonical union_form i j k ts1 ts2 f1 f2 :=
  Form (@union_pf i j k ts1 ts2 f1 f2).

Lemma empty_pf i : axiom i i [::] (empty_tag Unit).
Proof. by []. Qed.

Canonical empty_form i := Form (@empty_pf i).

Lemma pts_pf vars keys1 keys2 k v (f : xfind keys1 keys2 k):
        axiom (Context keys1 vars) (Context keys2 vars)
              [:: Pts k v] (key_tag (pts (xuntag f) v)).
Proof. by case: f=>p [E H]; split=>//=; rewrite ?E ?unitR // (onth_size E). Qed.

Canonical pts_form vars keys1 keys2 k v f :=
  Form (@pts_pf vars keys1 keys2 k v f).

Lemma var_pf keys vars1 vars2 n (f : xfind vars1 vars2 n) :
        axiom (Context keys vars1) (Context keys vars2)
              [:: Var T n] (var_tag (xuntag f)).
Proof. by case: f=>p [E H]; split=>//=; rewrite ?E ?unitR // (onth_size E). Qed.

Canonical var_form keys vars1 vars2 v f := Form (@var_pf keys vars1 vars2 v f).

End Syntactify.

Module Exports.
Coercion untag : tagged_map >-> UMC.sort.
Coercion pivot : form >-> tagged_map.
Canonical union_tag.
Canonical union_form.
Canonical empty_form.
Canonical pts_form.
Canonical var_form.
End Exports.
End Syntactify.

Export Syntactify.Exports.

Section ValidO.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (i : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Lemma validO j k ts1 ts2 (f1 : form (@empx K T U) j ts1)
                               (f2 : form j k ts2) :
        valid (untag f1) -> subterm ts2 ts1 -> valid (untag f2).
Proof.
case: f1 f2=>f1 [<- _ A1][f2][<- S2 A2] /= V; rewrite (sc_interp S2 A1) in V.
by case/(subterm_sound A2 (sc_wf S2 A1))=>xs /domeqP []; rewrite V=>/validL ->.
Qed.

End ValidO.

Arguments validO [K T U j k ts1 ts2 f1 f2] _ _.

Example ex0 (x y z : nat) (v1 v2 : nat) h:
          valid (Unit \+ y \\-> v1 \+ h \+ x \\-> v1) ->
          valid (x \\-> v2 \+ Unit).
Proof. by move=>V; rewrite (validO V). Abort.

Module ValidX.
Section ValidX.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (j : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_map (m : U) := Pack {unpack : U}.
Canonical equate (m : U) := Pack m m.

Definition raxiom j ts1 m (b : bool) (pivot : packed_map m) :=
  all (wf j) ts1 -> valid (interp j ts1) -> b -> valid (unpack pivot).

Structure rform j ts1 m b :=
  RForm {pivot :> packed_map m; _ : raxiom j ts1 b pivot}.

Lemma start_pf j k ts1 ts2 (f2 : form j k ts2) :
        @raxiom j ts1 (untag f2) (subterm ts2 ts1) (equate f2).
Proof.
case: f2=>f2 [<- S A2] A1; rewrite (sc_interp S A1)=>V.
case/(subterm_sound A2 (sc_wf S A1))=>xs.
by case/domeqP; rewrite V=>/validL ->.
Qed.

Canonical start j k ts1 ts2 f2 := RForm (@start_pf j k ts1 ts2 f2).

End ValidX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (j : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Lemma validX m j ts1 (f1 : form (empx U) j ts1) (g: rform j ts1 m true) :
        valid (untag f1) -> valid (unpack (pivot g)).
Proof. by case: g f1; case=>pivot H [f1][<- Sc A] /(H A); apply. Qed.

End Exports.

Arguments validX [K T U m j ts1 f1 g] _.

Example ex0 (x y z : nat) (v1 v2 : nat) h:
          valid (Unit \+ y \\-> v1 \+ h \+ x \\-> v1) ->
          valid (x \\-> v2 \+ Unit).
Proof. apply: validX. Abort.

End Exports.
End ValidX.

Export ValidX.Exports.

Section DomeqO.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (j : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Lemma domeqO j k rs1 rs2 ts1 ts2
         (f1 : form (empx U) j ts1) (f2 : form j k ts2) :
         subtract ts1 ts2 [::] = (rs1, rs2) ->
         dom_eq (pprint k (rev rs1)) (pprint k rs2) ->
         dom_eq (untag f1) (untag f2).
Proof.
case: f1 f2=>f1 [<- _ A1][f2][<- S A2].
case/(subtract_sound (sc_wf S A1) A2)=>// ys [/= D1 D2].
rewrite unitR in D1; rewrite (sc_interp S A1).
rewrite !pp_interp interp_rev => D; apply: domeq_trans D1 _.
rewrite domeq_sym; apply: domeq_trans D2 _.
by rewrite domeq_sym; apply: domeqUn.
Qed.

End DomeqO.

Example ex0 (x y z : nat) (v1 v2 : nat) h:
          dom_eq (Unit \+ y \\-> v1 \+ h \+ x \\-> v1) (x \\-> v2 \+ Unit).
Proof. apply: domeqO=>//=. Abort.

Module DomeqX.
Section DomeqX.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (j : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_map (m : U) := Pack {unpack : U}.
Canonical equate (m : U) := Pack m m.

Definition raxiom j k ts1 m b (pivot : packed_map m) :=
  all (wf j) ts1 -> sub_ctx j k /\
  (dom_eq (interp k b.1) (interp k b.2) ->
   dom_eq (interp k ts1) (unpack pivot)).

Structure rform j k ts1 m b :=
  RForm {pivot :> packed_map m; _ : raxiom j k ts1 b pivot}.

Lemma start_pf j k ts1 ts2 (f2 : form j k ts2) :
        @raxiom j k ts1 (untag f2) (subtract ts1 ts2 [::]) (equate f2).
Proof.
case: f2=>f2 [<- S A2]; case E : (subtract _ _ _)=>[rs1 rs2] A1; split=>//.
case/(subtract_sound (sc_wf S A1) A2): E=>ys [/= D1 D2 D].
rewrite unitR in D1; apply: domeq_trans D1 _.
rewrite domeq_sym; apply: domeq_trans D2 _.
by rewrite domeq_sym; apply: domeqUn.
Qed.

Canonical start j k ts1 ts2 f2 := RForm (@start_pf j k ts1 ts2 f2).

End DomeqX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (j : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Lemma domeqX m j k rs1 rs2 ts1 (f1 : form (empx U) j ts1)
                               (g : rform j k ts1 m (rs1, rs2)) :
        dom_eq (pprint k (rev rs1)) (pprint k rs2) ->
        dom_eq (untag f1) (unpack (pivot g)).
Proof.
case: g f1; case=>pivot R [f1][<- _ A1] /=; case/(_ A1): R=>S D.
by rewrite !pp_interp interp_rev (sc_interp S A1).
Qed.

End Exports.

Arguments domeqX [K T U m j k rs1 rs2 ts1 f1 g] _.

Example ex0 (x y z : nat) (v1 v2 : nat) h:
          dom_eq (Unit \+ y \\-> v1 \+ h \+ x \\-> v1) (x \\-> v2 \+ Unit).
Proof. apply: domeqX=>/=. Abort.

End Exports.
End DomeqX.

Export DomeqX.Exports.


Section InvalidO.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (i : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Lemma undefO i ts (f : form (empx U) i ts) :
        isundef i ts -> untag f = um_undef.
Proof. by case: f=>f [<- _ A] /(isundef_sound A)/invalidE. Qed.

Lemma invalidO i ts (f : form (empx U) i ts) :
        isundef i ts -> valid (untag f) = false.
Proof. by move/undefO=>->; rewrite valid_undef. Qed.

End InvalidO.

Example ex0 (x y z : nat) (v1 v2 : nat) h:
          (Unit \+ y \\-> v1 \+ h \+ y \\-> v1) = um_undef.
Proof. by apply: undefO. Abort.

Module InvalidX.
Section InvalidX.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (i : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Structure packed_map (m : U) := Pack {unpack : U}.
Canonical equate (m : U) := Pack m m.

Definition raxiom i ts m b (pivot : packed_map m) :=
  b -> valid (unpack pivot) = false.

Structure rform i ts m b :=
  RForm {pivot :> packed_map m; _ : raxiom i ts b pivot}.

Lemma start_pf i ts (f : form (empx U) i ts) :
        @raxiom i ts (untag f) (isundef i ts) (equate f).
Proof. by case: f=>f [<- S A] /(isundef_sound A) /negbTE. Qed.

Canonical start i ts f := RForm (@start_pf i ts f).

End InvalidX.

Module Exports.
Canonical equate.
Canonical start.

Section Exports.
Variables (K : ordType) (T : Type) (U : union_map_class K T).
Implicit Types (i : ctx U) (ts : seq (term T)).
Notation form := Syntactify.form.
Notation untag := Syntactify.untag.

Lemma undefX m i ts (g : rform i ts m true) : unpack (pivot g) = um_undef.
Proof. by case: g; case=>pivot /= /(_ (erefl _))/negbT/invalidE. Qed.

Lemma invalidX m i ts (g : rform i ts m true) :
        valid (unpack (pivot g)) = false.
Proof. by rewrite undefX valid_undef. Qed.

End Exports.

Arguments invalidX {K T U m i ts g}.

Example ex0 (x y z : nat) (v1 v2 : nat) h:
          valid (Unit \+ y \\-> v1 \+ h \+ y \\-> v1).
Proof. rewrite invalidX. Abort.

End Exports.
End InvalidX.

Export InvalidX.Exports.