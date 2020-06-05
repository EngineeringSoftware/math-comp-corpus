
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat seq.
From fourcolor
Require Import cfmap cfreducible configurations present.
From fourcolor
Require Import task001to214 task215to234 task235to282 task283to302 task303to322.
From fourcolor
Require Import task323to485 task486to506 task507to541 task542to588 task589to633.

Lemma the_reducibility : reducibility.
Proof.
rewrite /reducibility; apply cat_reducible_range with 322.
  CatReducible red000to214 red214to234 red234to282 red282to302 red302to322.
CatReducible red322to485 red485to506 red506to541 red541to588 red588to633.
Qed.