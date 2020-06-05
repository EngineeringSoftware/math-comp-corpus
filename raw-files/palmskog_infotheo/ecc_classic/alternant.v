
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype div prime bigop finset ssralg finalg.
From mathcomp Require Import binomial poly polydiv cyclic perm finfun matrix.
From mathcomp Require Import mxpoly vector mxalgebra zmodp finfield falgebra.
From mathcomp Require Import fieldext.

Require Import ssr_ext ssralg_ext vandermonde linearcode.
Require Import dft poly_decoding grs bch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Local Open Scope vec_ext_scope.

Section location_polynomial.

Variables (n : nat) (F : finFieldType) (a : 'rV[F]_n).

Definition location_polynomial_points :=
  \row_i \prod_(j < n | j != i) (a ``_ i - a ``_ j).

End location_polynomial.

Section grs_polynomial.

Variables (n : nat) (F : finFieldType) (a : 'rV[F]_n).
Variable g : {poly F}.
Let b := \row_(i < n) (((location_polynomial_points a) ``_ i)^-1 * g.[a ``_ i]).
Variable (r : nat).

Definition GRS_PCM_polynomial := @GRS.PCM _ F a b r.

End grs_polynomial.

Section injection_into_extension_field.

Variables (F0 : finFieldType) (F1 : fieldExtType F0).

Definition ext_inj : {rmorphism F0 -> F1} := @GRing.in_alg_rmorphism F0 F1.

Definition ext_inj_tmp : {rmorphism F0 -> (FinFieldExtType F1)} := ext_inj.

Variable n : nat.

Definition ext_inj_rV : 'rV[F0]_n -> 'rV[F1]_n := @map_mx _ _ ext_inj 1 n.

End injection_into_extension_field.

Section alternant_code.

Variable p u' : nat.
Let u := u'.+1.
Hypothesis primep : prime p.

Let Fq : finFieldType := GF u primep.
Let q := p ^ u.
Let p_char : p \in [char Fq].
Proof. apply char_GFqm. Qed.

Variable m' : nat.
Let m := m'.+1.
Variable Fqm : fieldExtType Fq.
Hypothesis card_Fqm : #| FinFieldExtType Fqm | = q ^ m.

Variable n : nat.
Variable a : 'rV[Fqm]_n.
Variable g : {poly Fqm}.
Variable k : nat.

Definition alternant_PCM : 'M_(k, n) := @GRS_PCM_polynomial n (FinFieldExtType Fqm) a g k.

Definition alternant_code := Rcode.t (@ext_inj_tmp Fq Fqm) (kernel alternant_PCM).

Definition goppa_code_condition := size g = (n - k).+1.

End alternant_code.

Section narrow_sense_BCH_are_Goppa.

Variable p u' : nat.
Let u := u'.+1.
Hypothesis primep : prime p.

Let Fq : finFieldType := GF u primep.
Let q := p ^ u.
Let p_char : p \in [char Fq].
Proof. apply char_GFqm. Qed.

Variable m' : nat.
Let m := m'.+1.
Variable Fqm : fieldExtType Fq.
Hypothesis card_Fqm : #| FinFieldExtType Fqm | = q ^ m.

Let n : nat := (q^m).-1.
Variable e : Fqm.
Hypothesis e_prim : n.-primitive_root e.
Let a : 'rV[Fqm]_n := rVexp e n.
Variable t : nat.

Let g : {poly (FinFieldExtType Fqm)} := 'X^(n - t).

Let goppa_code_condition_check : goppa_code_condition n g t.
Proof. by rewrite /goppa_code_condition size_polyXn. Qed.

Lemma narrow_sense_BCH_are_Goppa :
  @BCH.PCM (FinFieldExtType _) _ a t =
  @alternant_PCM _ u' primep Fqm _ a g t.
Proof.
rewrite /BCH.code /alternant_code.
Abort.

End narrow_sense_BCH_are_Goppa.