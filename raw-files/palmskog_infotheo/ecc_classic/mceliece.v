
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop prime ssralg.
From mathcomp Require Import poly polydiv finset fingroup perm finalg zmodp.
From mathcomp Require Import matrix mxalgebra mxpoly vector.
Require Import ssralg_ext hamming linearcode decoding channel_code.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Module McEliece.

Section mceliece.

Variable k n' : nat.
Let n := n'.+1.
Variable Hdimlen : k <= n.
Variable CSM : 'M['F_2]_(n - k, k).
Local Notation "'H" := (Syslcode.PCM Hdimlen CSM).
Local Notation "'G" := (Syslcode.GEN Hdimlen CSM).
Let encode := Syslcode.encode Hdimlen CSM.

Parameter repair : repairT [finType of 'F_2] [finType of 'F_2] n.
Variable repair_img : oimg repair \subset kernel 'H.
Parameter discard : discardT [finType of 'F_2] n [finType of 'rV['F_2]_k].
Parameter encode_discard : cancel_on (kernel 'H) encode discard.

Definition C := Syslcode.t repair_img encode_discard.
Let decode := Decoder.dec (Lcode.dec C).

Parameter t : nat.

Local Open Scope ecc_scope.

Variable bdd : t.-BDD (C, repair).

Parameter S : 'M['F_2]_k.
Variable S_inv : S \in unitmx.
Parameter p : 'S_n.
Definition P : 'M['F_2]_n := perm_mx p.

Definition pubkey : 'M_(k, n) := S *m 'G *m P.

Parameter msg : 'rV['F_2]_k.
Parameter z : 'rV['F_2]_n.
Parameter Hz : wH z = t.

Definition cyp : 'rV_n := msg *m pubkey + z.

Definition cyp_hat : 'rV_n := cyp *m P^-1.

Variable msg_hat : {m | decode cyp_hat = Some m}.

Definition msg' : 'rV_k := proj1_sig msg_hat *m invmx S.

Lemma decryption_undoes_encryption : msg = msg'.
Proof.
rewrite /msg'.
destruct msg_hat as [msg_hat' Hmsg_hat] => /=.
have : decode cyp_hat = Some (msg *m S).
  have -> : cyp_hat = (msg *m S) *m 'G + (z *m P^-1).
    rewrite /cyp_hat /cyp /pubkey mulmxDl -!mulmxA mulmxV ?mulmx1 //.
    by apply: unitmx_perm.
  rewrite ffunE /=.
  have H : msg *m S *m 'G \in kernel 'H.
    move/subsetP: (Encoder.enc_img (Lcode.enc C)); apply.
    apply/imsetP; exists (msg *m S) => //.
    by rewrite ffunE.
  move: bdd => /=; rewrite /bdd /= => -> //; last first.
    by rewrite /P -perm_mxV wH_perm_mx Hz.
  move: (@encode_discard (msg *m S *m 'G) H).
  rewrite ffunE => K.
  congr Some.
  apply: (@Syslcode.encode_inj _ _ _ Hdimlen CSM).
  by rewrite ffunE /= /Syslcode.encode ffunE.
rewrite Hmsg_hat => -[] ->.
rewrite -mulmxA mulmxV ?mulmx1 //; exact S_inv.
Qed.

End mceliece.

End McEliece.