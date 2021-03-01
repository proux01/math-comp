(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop order ssralg poly ssrnum ssrint.

(******************************************************************************)
(* This file defines some numeric structures extended with the Archimedean    *)
(* axiom. To use this file, insert "Import Num.Theory." and optionally        *)
(* "Import Num.Def." before your scripts as in the ssrnum library. These      *)
(* modules provided by this library subsumes those of ssrnum.                 *)
(*                                                                            *)
(* NB: the Archimedean structures are actually defined in ssrnum, but they    *)
(* are deprecated in ssrnum and will be relocated to this file in a future    *)
(* release.                                                                   *)
(*                                                                            *)
(*   * ArchiNumDomain (Num Domain with the Archimedean axiom)                 *)
(*     archiNumDomainType                                                     *)
(*                  == interface for an Archimedean num domain.               *)
(*     ArchiNumDomainType T r                                                 *)
(*                  == packs the archimeadean axiom r into a                  *)
(*                     ArchiNumDomainType. The carrier T must have a num      *)
(*                     domain type structure.                                 *)
(*    [archiNumDomainType of T for S ]                                        *)
(*                  == T-clone of the archiNumDomainType structure  S.        *)
(*    [archiNumDomainType of T]                                               *)
(*                  == clone of a canonical archiNumDomainType structure      *)
(*                     on T.                                                  *)
(*                                                                            *)
(*   * ArchiNumField (Num Field with the Archimedean axiom)                   *)
(*     archiNumFieldType                                                      *)
(*                  == interface for an Archimedean num field.                *)
(*    [archiNumFieldType of T]                                                *)
(*                  == clone of a canonical archiNumFieldType structure on T. *)
(*                                                                            *)
(*   * ArchiNumClosedField (Num Closed Field with the Archimedean axiom)      *)
(*     archiNumClosedFieldType                                                *)
(*                  == interface for an Archimedean num closed field.         *)
(*    [archiNumClosedFieldType of T]                                          *)
(*                  == clone of a canonical archiNumClosedFieldType           *)
(*                     structure on T.                                        *)
(*                                                                            *)
(*   * ArchiRealDomain (Real Domain with the Archimedean axiom)               *)
(*     archiRealDomainType                                                    *)
(*                  == interface for an Archimedean real domain.              *)
(*    [archiRealDomainType of T]                                              *)
(*                  == clone of a canonical archiRealDomainType structure     *)
(*                     on T.                                                  *)
(*                                                                            *)
(*   * ArchiRealField (Real Field with the Archimedean axiom)                 *)
(*     archiRealFieldType                                                     *)
(*                  == interface for an Archimedean real field.               *)
(*    [archiRealFieldType of T]                                               *)
(*                  == clone of a canonical archiRealFieldType structure on T.*)
(*                                                                            *)
(*   * ArchiRealClosedField (Real Closed Field with the Archimedean axiom)    *)
(*     archiRcfType == interface for an Archimedean real closed field.        *)
(*    [archiRcfType of T]                                                     *)
(*                  == clone of a canonical archiRcfType structure on T.      *)
(*                                                                            *)
(* Over these structures, we have the following operations:                   *)
(*     x \is a Num.int <=> x is an integer, i.e., x = m%:~R for some m : int. *)
(*     x \is a Num.nat <=> x is a natual number, i.e., x = m%:R for some      *)
(*                         m : nat.                                           *)
(*         Num.floor x == for x \in Num.real, an m : int such that            *)
(*                        m%:~R <= z < (m + 1)%:~R, else 0%Z.                 *)
(*          Num.ceil x == for x \in Num.real, an m : int such that            *)
(*                        (m%:~R - 1)%:~R < z <= m%:~R, else 0%Z.             *)
(*         Num.trunc x == for x >= 0, an n : nat such that                    *)
(*                        n%:R <= z < n.+1%:R, else 0%N.                      *)
(*         Num.bound x == upper bound for x, i.e., n such that `|x| < n%:R.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Theory.

Module Num.

Module Import Exports.

Notation archiNumDomainType := Num.ArchiNumDomain.type.
Notation "[ 'archiNumDomainType' 'of' T 'for' cT ]" :=
  (@Num.ArchiNumDomain.clone T cT _ idfun)
  (at level 0, format "[ 'archiNumDomainType'  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'archiNumDomainType' 'of' T ]" :=
  (@Num.ArchiNumDomain.clone T _ _ id)
  (at level 0, format "[ 'archiNumDomainType'  'of'  T ]") : form_scope.

Notation archiNumFieldType := Num.ArchiNumField.type.
Notation "[ 'archiNumFieldType' 'of' T ]" :=
  (@Num.ArchiNumField.pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiNumFieldType'  'of'  T ]") : form_scope.

Notation archiNumClosedFieldType := Num.ArchiNumClosedField.type.
Notation "[ 'archiNumClosedFieldType' 'of' T ]" :=
  (@Num.ArchiNumClosedField.pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiNumClosedFieldType'  'of'  T ]") : form_scope.

Notation archiRealDomainType := Num.ArchiRealDomain.type.
Notation "[ 'archiRealDomainType' 'of' T ]" :=
  (@Num.ArchiRealDomain.pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiRealDomainType'  'of'  T ]") : form_scope.

Notation archiRealFieldType := Num.ArchiRealField.type.
Notation "[ 'archiRealFieldType' 'of' T ]" :=
  (@Num.ArchiRealField.pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiRealFieldType'  'of'  T ]") : form_scope.

Notation archiRcfType := Num.ArchiRealClosedField.type.
Notation "[ 'archiRcfType' 'of' T ]" :=
  (@Num.ArchiRealClosedField.pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiRcfType'  'of'  T ]") : form_scope.

End Exports.

Module Import Internals.

Section ArchiNumDomain.
Variable R : archiNumDomainType.
Implicit Types x y : R.

Local Notation trunc := (@Num.Def.truncR R).

Definition truncRP x :
  if 0 <= x then (trunc x)%:R <= x < (trunc x).+1%:R else trunc x == 0%N :=
  Num.Internals.truncRP x.

Definition truncR_itv x : 0 <= x -> (trunc x)%:R <= x < (trunc x).+1%:R :=
  @Num.Internals.truncR_itv R x.

Fact floorR_subproof x :
  {m | if x \is Num.real then m%:~R <= x < (m + 1)%:~R else m == 0}.
Proof.
have [Rx | _] := boolP (x \is Num.real); last by exists 0.
without loss x_ge0: x Rx / x >= 0.
  have [x_ge0 | /ltW x_le0] := real_ge0P Rx; first exact.
  case/(_ (- x)) => [||m]; rewrite ?rpredN ?oppr_ge0 //.
  rewrite ler_oppr ltr_oppl -!rmorphN opprD /= le_eqVlt.
  case: eqP => [-> _ | _ /andP[lt_x_m lt_m_x]].
    by exists (- m); rewrite lexx rmorphD ltr_addl ltr01.
  by exists (- m - 1); rewrite (ltW lt_m_x) subrK.
by exists (Posz (trunc x)); rewrite addrC -intS -!pmulrn truncR_itv.
Qed.

End ArchiNumDomain.

End Internals.

Module Import Def.
Export ssrnum.Num.Def.
Definition floorR {R : archiNumDomainType} (x : R) := sval (floorR_subproof x).
Definition ceilR {R : archiNumDomainType} (x : R) := - floorR (- x).
End Def.

Notation trunc := truncR.
Notation floor := floorR.
Notation ceil := ceilR.
Notation bound := Num.ExtraDef.archi_bound.

Module Import Theory.
Export ssrnum.Num.Theory.

Section ArchiNumDomainTheory.

Variable R : archiNumDomainType.
Implicit Types x y z : R.

Local Notation trunc := (@Num.trunc R).
Local Notation floor := (@Num.floor R).
Local Notation ceil := (@Num.ceil R).
Local Notation Rnat := (@Rnat R).
Local Notation Rint := (@Rint R).

(* trunc and Rnat *)

Definition truncR_itv x : 0 <= x -> (trunc x)%:R <= x < (trunc x).+1%:R :=
  @truncR_itv R x.

Lemma RnatE x : (x \is a Rnat) = ((truncR x)%:R == x).
Proof. by case: R x => ? [? []]. Qed.

Definition archi_boundP x : 0 <= x -> x < (bound x)%:R :=
  @ssrnum.Num.Theory.mc_1_12.archi_boundP R x.

Lemma truncR_def x n : n%:R <= x < n.+1%:R -> trunc x = n.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eqn_leq -ltnS -[(n <= _)%N]ltnS.
have/truncR_itv/andP[lefx ltxf1]: 0 <= x by apply: le_trans lemx; apply: ler0n.
by rewrite -!(ltr_nat R) 2?(@le_lt_trans _ _ x).
Qed.

Lemma natRK : cancel (GRing.natmul 1) trunc.
Proof. by move=> m; apply: truncR_def; rewrite ler_nat ltr_nat ltnS leqnn. Qed.

Lemma truncRK : {in Rnat, cancel trunc (GRing.natmul 1)}.
Proof. by move=> x; rewrite RnatE => /eqP. Qed.

Lemma truncR0 : trunc 0 = 0%N. Proof. exact: natRK 0%N. Qed.
Lemma truncR1 : trunc 1 = 1%N. Proof. exact: natRK 1%N. Qed.
Hint Resolve truncR0 truncR1 : core.

Lemma Rnat_nat n : n%:R \is a Rnat. Proof. by rewrite RnatE natRK. Qed.
Hint Resolve Rnat_nat : core.

Lemma RnatP x : reflect (exists n, x = n%:R) (x \is a Rnat).
Proof.
apply: (iffP idP) => [|[n ->]]; rewrite // RnatE => /eqP <-.
by exists (trunc x).
Qed.

Lemma truncRD : {in Rnat & Rnneg, {morph trunc : x y / x + y >-> (x + y)%N}}.
Proof.
move=> _ y /RnatP[n ->] y_ge0; apply: truncR_def.
by rewrite -addnS !natrD !natRK ler_add2l ltr_add2l truncR_itv.
Qed.

Lemma truncRM : {in Rnat &, {morph trunc : x y / x * y >-> (x * y)%N}}.
Proof. by move=> _ _ /RnatP[n1 ->] /RnatP[n2 ->]; rewrite -natrM !natRK. Qed.

Lemma truncRX n : {in Rnat, {morph trunc : x / x ^+ n >-> (x ^ n)%N}}.
Proof. by move=> _ /RnatP[n1 ->]; rewrite -natrX !natRK. Qed.

Lemma rpred_Rnat S (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  x \is a Rnat -> x \in kS.
Proof. by move=> /RnatP[n ->]; apply: rpred_nat. Qed.

Lemma Rnat0 : 0 \is a Rnat. Proof. exact: (Rnat_nat 0). Qed.
Lemma Rnat1 : 1 \is a Rnat. Proof. exact: (Rnat_nat 1). Qed.
Hint Resolve Rnat0 Rnat1 : core.

Fact Rnat_semiring : semiring_closed Rnat.
Proof.
by do 2![split] => //= _ _ /RnatP[n ->] /RnatP[m ->]; rewrite -(natrD, natrM).
Qed.
Canonical Rnat_addrPred := AddrPred Rnat_semiring.
Canonical Rnat_mulrPred := MulrPred Rnat_semiring.
Canonical Rnat_semiringPred := SemiringPred Rnat_semiring.

Lemma Rreal_Rnat : {subset Rnat <= Rreal}. Proof. by move=> _ /RnatP[m ->]. Qed.

Lemma Rnat_normK x : x \is a Rnat -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Rreal_Rnat/real_normK. Qed.

Lemma truncR_gt0 x : (0 < trunc x)%N = (1 <= x).
Proof.
case: ifP (truncRP x) => [le0x /andP[lemx ltxm1] | le0x /eqP ->]; last first.
  by apply/esym; apply/contraFF/le_trans: le0x.
apply/idP/idP => [m_gt0 | x_ge1]; first by apply: le_trans lemx; rewrite ler1n.
by rewrite -ltnS -(ltr_nat R) (le_lt_trans x_ge1).
Qed.

Lemma truncR0Pn x : reflect (trunc x = 0%N) (~~ (1 <= x)).
Proof. by rewrite -truncR_gt0 -eqn0Ngt; apply: eqP. Qed.

Lemma Rnat_ge0 x : x \is a Rnat -> 0 <= x.
Proof. by move=> /RnatP[n ->]; apply: ler0n. Qed.

Lemma Rnat_gt0 x : x \is a Rnat -> (0 < x) = (x != 0).
Proof. by move=> /RnatP[n ->]; rewrite pnatr_eq0 ltr0n lt0n. Qed.

Lemma norm_Rnat x : x \is a Rnat -> `|x| = x.
Proof. by move/Rnat_ge0/ger0_norm. Qed.

Lemma Rnat_sum_eq1 (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> F i \is a Rnat) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof.
move=> natF sumF1; pose nF i := trunc (F i).
have{natF} defF i: P i -> F i = (nF i)%:R by move/natF; rewrite RnatE => /eqP.
have{sumF1} /eqP sumF1: (\sum_(i | P i) nF i == 1)%N.
  by rewrite -(@eqr_nat R) natr_sum -(eq_bigr _ defF) sumF1.
have [i Pi nZfi]: {i : I | P i & nF i != 0%N}.
  by apply/sig2W/exists_inP; rewrite -negb_forall_in -sum_nat_eq0 sumF1.
have F'ge0 := (leq0n _, etrans (eq_sym _ _) (sum_nat_eq0 (predD1 P i) nF)).
rewrite -lt0n in nZfi; have [_] := (leqif_add (leqif_eq nZfi) (F'ge0 _)).
rewrite /= big_andbC -bigD1 // sumF1 => /esym/andP/=[/eqP Fi1 /forall_inP Fi'0].
exists i; split=> // [|j neq_ji Pj]; first by rewrite defF // -Fi1.
by rewrite defF // (eqP (Fi'0 j _)) // neq_ji.
Qed.

Lemma Rnat_mul_eq1 x y :
  x \is a Rnat -> y \is a Rnat -> (x * y == 1) = (x == 1) && (y == 1).
Proof. by do 2!move/truncRK <-; rewrite -natrM !pnatr_eq1 muln_eq1. Qed.

Lemma Rnat_prod_eq1 (I : finType) (P : pred I) (F : I -> R) :
    (forall i, P i -> F i \is a Rnat) -> \prod_(i | P i) F i = 1 ->
  forall i, P i -> F i = 1.
Proof.
move=> natF prodF1; apply/eqfun_inP; rewrite -big_andE.
move: prodF1; elim/(big_load (fun x => x \is a Rnat)): _.
elim/big_rec2: _ => // i all1x x /natF N_Fi [Nx x1all1].
by split=> [|/eqP]; rewrite ?rpredM ?Rnat_mul_eq1 // => /andP[-> /eqP].
Qed.

(* floor and Rint *)

Local Lemma floorRP x :
  if x \is Rreal then
    (floor x)%:~R <= x < (floor x + 1)%:~R else floor x == 0%N.
Proof. by rewrite /floor; case: (floorR_subproof x). Qed.

Lemma RintE x : (x \is a Rint) = (x \is a Rnat) || (- x \is a Rnat).
Proof. by case: R x => ? [? []]. Qed.

Lemma floorR_itv x : x \is Rreal -> (floor x)%:~R <= x < (floor x + 1)%:~R.
Proof. by case: (x \is _) (floorRP x). Qed.

Lemma ge_floorR x : x \is Rreal -> (floor x)%:~R <= x.
Proof. by move=> /floorR_itv /andP[]. Qed.

Lemma lt_succ_floorR x : x \is Rreal -> x < (floor x + 1)%:~R.
Proof. by move=> /floorR_itv /andP[]. Qed.

Lemma floorR_def x m : m%:~R <= x < (m + 1)%:~R -> floor x = m.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eq_le -!ltz_addr1.
move: (ger_real lemx); rewrite realz => /floorR_itv/andP[lefx ltxf1].
by rewrite -!(ltr_int R) 2?(@le_lt_trans _ _ x).
Qed.

Lemma floorR_ge_int x n : x \is Rreal -> n%:~R <= x = (n <= floor x).
Proof.
move=> /floorR_itv /andP[lefx ltxf1]; apply/idP/idP => lenx.
  by rewrite -ltz_addr1 -(ltr_int R); apply: le_lt_trans ltxf1.
by apply: le_trans lefx; rewrite ler_int.
Qed.

Lemma floorR_le : {homo floor : x y / x <= y}.
Proof.
move=> x y lexy; move: (floorRP x) (floorRP y); rewrite (ger_real lexy).
case: ifP => [_ /andP[lefx _] /andP[_] | _ /eqP-> /eqP-> //].
by move=> /(le_lt_trans lexy) /(le_lt_trans lefx); rewrite ltr_int ltz_addr1.
Qed.

Lemma intRK : cancel intr floor.
Proof. by move=> m; apply: floorR_def; rewrite lexx rmorphD ltr_addl ltr01. Qed.

Lemma Rint_int m : m%:~R \is a Rint.
Proof. by rewrite RintE; case: m => n; rewrite ?opprK Rnat_nat ?orbT. Qed.

Lemma RintP x : reflect (exists m, x = m%:~R) (x \is a Rint).
Proof.
apply: (iffP idP) => [x_int | [m ->]]; last exact: Rint_int.
rewrite -[x]opprK; move: x_int; rewrite RintE.
move=> /orP[] /RnatP[n ->]; first by exists n; rewrite opprK.
by exists (- n%:R); rewrite mulrNz mulrz_nat.
Qed.

Lemma Rint_def x : x \is a Rint = ((floor x)%:~R == x).
Proof.
by apply/RintP/eqP => [[n ->] | <-]; [rewrite intRK | exists (floor x)].
Qed.

Lemma floorRK : {in Rint, cancel floor intr}.
Proof. by move=> z; rewrite Rint_def => /eqP. Qed.

Lemma floorR0 : floor 0 = 0. Proof. exact: intRK 0. Qed.
Lemma floorR1 : floor 1 = 1. Proof. exact: intRK 1. Qed.
Hint Resolve floorR0 floorR1 : core.

Lemma floorRD : {in Rint & Rreal, {morph floor : x y / x + y}}.
Proof.
move=> _ y /RintP[m ->] Ry; apply: floorR_def.
by rewrite -addrA 2!rmorphD /= intRK ler_add2l ltr_add2l floorR_itv.
Qed.

Lemma floorRN : {in Rint, {morph floor : x / - x}}.
Proof. by move=> _ /RintP[m ->]; rewrite -rmorphN !intRK. Qed.

Lemma floorRM : {in Rint &, {morph floor : x y / x * y}}.
Proof. by move=> _ _ /RintP[m1 ->] /RintP[m2 ->]; rewrite -rmorphM !intRK. Qed.

Lemma floorRX n : {in Rint, {morph floor : x / x ^+ n}}.
Proof. by move=> _ /RintP[m ->]; rewrite -rmorphX !intRK. Qed.

(* ceil and Rint *)

Lemma ceilR_itv x : x \is Rreal -> (ceil x - 1)%:~R < x <= (ceil x)%:~R.
Proof.
by move=> Rx; rewrite -opprD !mulrNz ltr_oppl ler_oppr andbC floorR_itv ?realN.
Qed.

Lemma gt_pred_ceilR x : x \is Rreal -> (ceil x - 1)%:~R < x.
Proof. by move=> /ceilR_itv /andP[]. Qed.

Lemma le_ceilR x : x \is Rreal -> x <= (ceil x)%:~R.
Proof. by move=> /ceilR_itv /andP[]. Qed.

Lemma ceilR_def x m : (m - 1)%:~R < x <= m%:~R -> ceil x = m.
Proof.
move=> Hx; apply/eqP; rewrite eqr_oppLR; apply/eqP/floorR_def.
by rewrite ler_oppr ltr_oppl andbC -!mulrNz opprD opprK.
Qed.

Lemma ceilR_le_int x n : x \is Rreal -> x <= n%:~R = (ceil x <= n).
Proof.
rewrite -realN; move=> /(floorR_ge_int (- n)).
by rewrite mulrNz ler_oppl opprK => ->; rewrite ler_oppl.
Qed.

Lemma ceilR_le : {homo ceil : x y / x <= y}.
Proof. by move=> x y lexy; rewrite /ceil ler_opp2 floorR_le ?ler_opp2. Qed.

Lemma floor_ceil x : x \is Rreal -> ceil x = floor x + (~~ (x \is a Rint)).
Proof.
case Ix: (x \is a Rint) => Rx /=.
  by apply/eqP; rewrite addr0 eqr_oppLR floorRN.
apply/ceilR_def; rewrite addrK; move: (floorR_itv Rx).
by rewrite le_eqVlt -Rint_def Ix /= => /andP[-> /ltW].
Qed.

Lemma intRK' : cancel intr ceil.
Proof. by move=> m; apply/eqP; rewrite eqr_oppLR -mulrNz intRK. Qed.

Lemma Rint_def' x : x \is a Rint = ((ceil x)%:~R == x).
Proof. by rewrite mulrNz eqr_oppLR -Rint_def !RintE opprK orbC. Qed.

Lemma ceilRK : {in Rint, cancel ceil intr}.
Proof. by move=> z; rewrite Rint_def' => /eqP. Qed.

Lemma ceilR0 : ceil 0 = 0. Proof. exact: intRK' 0. Qed.
Lemma ceilR1 : ceil 1 = 1. Proof. exact: intRK' 1. Qed.
Hint Resolve ceilR0 ceilR1 : core.

Lemma ceilRD : {in Rint & Rreal, {morph ceil : x y / x + y}}.
Proof.
move=> _ y /RintP[m ->] Ry; apply: ceilR_def.
by rewrite -addrA 3!rmorphD /= intRK' ler_add2l ltr_add2l -rmorphD ceilR_itv.
Qed.

Lemma ceilRN : {in Rint, {morph ceil : x / - x}}.
Proof. by move=> _ /RintP[m ->]; rewrite -rmorphN !intRK'. Qed.

Lemma ceilRM : {in Rint &, {morph ceil : x y / x * y}}.
Proof. by move=> _ _ /RintP[m1 ->] /RintP[m2 ->]; rewrite -rmorphM !intRK'. Qed.

Lemma ceilRX n : {in Rint, {morph ceil : x / x ^+ n}}.
Proof. by move=> _ /RintP[m ->]; rewrite -rmorphX !intRK'. Qed.

Lemma rpred_Rint S (ringS : subringPred S) (kS : keyed_pred ringS) x :
  x \is a Rint -> x \in kS.
Proof. by move=> /RintP[n ->]; rewrite rpred_int. Qed.

Lemma Rint0 : 0 \is a Rint. Proof. by rewrite RintE Rnat0. Qed.
Lemma Rint1 : 1 \is a Rint. Proof. by rewrite RintE Rnat1. Qed.
Hint Resolve Rint0 Rint1 : core.

Fact Rint_subring : subring_closed Rint.
Proof.
by split=> // ? ? /RintP[n ->] /RintP[m ->]; rewrite -?mulrzBr -?intrM Rint_int.
Qed.
Canonical Rint_opprPred := OpprPred Rint_subring.
Canonical Rint_addrPred := AddrPred Rint_subring.
Canonical Rint_mulrPred := MulrPred Rint_subring.
Canonical Rint_zmodPred := ZmodPred Rint_subring.
Canonical Rint_semiringPred := SemiringPred Rint_subring.
Canonical Rint_smulrPred := SmulrPred Rint_subring.
Canonical Rint_subringPred := SubringPred Rint_subring.

Lemma Rint_Rnat : {subset Rnat <= Rint}.
Proof. by move=> ?; rewrite RintE => ->. Qed.

Lemma Rreal_Rint : {subset Rint <= Rreal}. Proof. exact: rpred_Rint. Qed.

Lemma Rint_normK x : x \is a Rint -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Rreal_Rint/real_normK. Qed.

Lemma RintEsign x : x \is a Rint -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by move/Rreal_Rint/realEsign. Qed.

Lemma Rnat_norm_Rint x : x \is a Rint -> `|x| \is a Rnat.
Proof. by move=> /RintP[m ->]; rewrite -intr_norm rpred_nat. Qed.

Lemma RnatEint x : (x \is a Rnat) = (x \is a Rint) && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite Rint_Rnat ?Rnat_ge0.
by rewrite -(ger0_norm x_ge0) Rnat_norm_Rint.
Qed.

Lemma RintEge0 x : 0 <= x -> (x \is a Rint) = (x \is a Rnat).
Proof. by rewrite RnatEint andbC => ->. Qed.

Lemma Rnat_exp_even x n : ~~ odd n -> x \is a Rint -> x ^+ n \is a Rnat.
Proof.
move=> n_oddF x_Rint.
by rewrite RnatEint rpredX //= real_exprn_even_ge0 // Rreal_Rint.
Qed.

Lemma norm_Rint_ge1 x : x \is a Rint -> x != 0 -> 1 <= `|x|.
Proof.
rewrite -normr_eq0 => /Rnat_norm_Rint/RnatP[n ->].
by rewrite pnatr_eq0 ler1n lt0n.
Qed.

Lemma sqr_Rint_ge1 x : x \is a Rint -> x != 0 -> 1 <= x ^+ 2.
Proof.
by move=> Zx nz_x; rewrite -Rint_normK // expr_ge1 ?normr_ge0 ?norm_Rint_ge1.
Qed.

Lemma Rint_ler_sqr x : x \is a Rint -> x <= x ^+ 2.
Proof.
move=> Zx; have [-> | nz_x] := eqVneq x 0; first by rewrite expr0n.
apply: le_trans (_ : `|x| <= _); first by rewrite real_ler_norm ?Rreal_Rint.
by rewrite -Rint_normK // ler_eexpr // norm_Rint_ge1.
Qed.

Lemma floorRpK : {in polyOver Rint, cancel (map_poly floor) (map_poly intr)}.
Proof.
move=> p /(all_nthP 0) Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/floorRK // | _]; rewrite floorR0.
Qed.

Lemma floorRpP (p : {poly R}) :
  p \is a polyOver Rint -> {q | p = map_poly intr q}.
Proof. by exists (map_poly floor p); rewrite floorRpK. Qed.

(* Relating Cnat and oldCnat. *)

Lemma truncR_old x : trunc x = if 0 <= x then `|floor x|%N else 0%N.
Proof.
case: ifP => [x_ge0 | x_ge0F]; last first.
  by apply/truncR0Pn; apply/contraFN: x_ge0F; apply/le_trans.
apply/truncR_def; rewrite !pmulrn intS addrC abszE; have/floorR_le := x_ge0.
by rewrite floorR0 => /normr_idP ->; exact/floorR_itv/ger0_real.
Qed.

(* predCmod *)
Variables (U V : lmodType R) (f : {additive U -> V}).

Lemma raddfZ_Rnat a u : a \is a Rnat -> f (a *: u) = a *: f u.
Proof. by move=> /RnatP[n ->]; apply: raddfZnat. Qed.

Lemma rpredZ_Rnat S (addS : @addrPred V S) (kS : keyed_pred addS) :
  {in Rnat & kS, forall z u, z *: u \in kS}.
Proof. by move=> _ u /RnatP[n ->]; apply: rpredZnat. Qed.

Lemma raddfZ_Rint a u : a \is a Rint -> f (a *: u) = a *: f u.
Proof. by move=> /RintP[m ->]; rewrite !scaler_int raddfMz. Qed.

Lemma rpredZ_Rint S (subS : @zmodPred V S) (kS : keyed_pred subS) :
  {in Rint & kS, forall z u, z *: u \in kS}.
Proof. by move=> _ u /RintP[m ->] ?; rewrite scaler_int rpredMz. Qed.

(* autC *)
Implicit Type nu : {rmorphism R -> R}.

Lemma aut_Rnat nu : {in Rnat, nu =1 id}.
Proof. by move=> _ /RnatP[n ->]; apply: rmorph_nat. Qed.

Lemma aut_Rint nu : {in Rint, nu =1 id}.
Proof. by move=> _ /RintP[m ->]; apply: rmorph_int. Qed.

End ArchiNumDomainTheory.

Arguments natRK {R} _%N.
Arguments intRK {R}.
Arguments RnatP {R x}.
Arguments RintP {R x}.
Hint Resolve truncR0 truncR1 : core.
Hint Resolve floorR0 floorR1 : core.
Hint Extern 0 (is_true (_%:R \is a Rnat)) => apply: Rnat_nat : core.
Hint Extern 0 (is_true (_%:~R \is a Rint)) => apply: Rint_int : core.
Hint Extern 0 (is_true (0 \is a Rnat)) => apply: Rnat0 : core.
Hint Extern 0 (is_true (1 \is a Rnat)) => apply: Rnat1 : core.
Hint Extern 0 (is_true (0 \is a Rint)) => apply: Rint0 : core.
Hint Extern 0 (is_true (1 \is a Rint)) => apply: Rint1 : core.

Section ArchiRealDomainTheory.

Variables (R : archiRealDomainType).

Definition upper_nthrootP (x : R) i : (bound x <= i)%N -> x < 2%:R ^+ i :=
  @ssrnum.Num.Theory.mc_1_12.upper_nthrootP R x i.

End ArchiRealDomainTheory.

Section ArchiNumFieldTheory.

Variable R : archiNumFieldType.

(* autLmodC *)
Implicit Type nu : {rmorphism R -> R}.

Lemma Rnat_aut nu x : (nu x \is a Rnat) = (x \is a Rnat).
Proof. by apply/idP/idP=> /[dup] ? /(aut_Rnat nu) => [/fmorph_inj <-| ->]. Qed.

Lemma Rint_aut nu x : (nu x \is a Rint) = (x \is a Rint).
Proof. by rewrite !RintE -rmorphN !Rnat_aut. Qed.

End ArchiNumFieldTheory.

Section ArchiNumClosedFieldTheory.

Variable R : archiNumClosedFieldType.

Implicit Type x : R.

Lemma conj_Rnat x : x \is a Rnat -> x^* = x.
Proof. by move/Rreal_Rnat/CrealP. Qed.

Lemma conj_Rint x : x \is a Rint -> x^* = x.
Proof. by move/Rreal_Rint/CrealP. Qed.

End ArchiNumClosedFieldTheory.

Section ZnatPred.

Notation Znat_def := ssrint.mc_1_12.Znat_def.
Notation ZnatP := ssrint.mc_1_12.ZnatP.

End ZnatPred.

End Theory.

Module PredInstances.
Canonical Rnat_addrPred.
Canonical Rnat_mulrPred.
Canonical Rnat_semiringPred.
Canonical Rint_opprPred.
Canonical Rint_addrPred.
Canonical Rint_mulrPred.
Canonical Rint_zmodPred.
Canonical Rint_semiringPred.
Canonical Rint_smulrPred.
Canonical Rint_subringPred.
End PredInstances.

Notation nat := Rnat.
Notation int := Rint.

End Num.

Export Num.ArchiNumDomain.Exports Num.ArchiNumField.Exports.
Export Num.ArchiNumClosedField.Exports Num.ArchiRealDomain.Exports.
Export Num.ArchiRealField.Exports Num.ArchiRealClosedField.Exports.
Export Num.ArchiMixin.Exports Num.Exports Num.PredInstances.
