From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint rat.

Import GRing.Theory.

Local Open Scope ring_scope.

Section DemoCoercionsNatmul.

Variable R : ringType.

Variables (x : R) (n : nat).

Lemma test_nat : n + x + 1 = x + n.+1.
Proof.
(* n + x + 1 = x + n.+1 *)
rewrite -addn1.
(* n + x + 1 = x + (n + 1)%:R *)
rewrite natrD.
(* n + x + 1 = x + (n + 1) *)
by rewrite addrCA addrA.
Qed.

(* but %:R needs to be printed on LHS of equalities *)
Check n%:R = x.
Check n%:R <> x.
Check n%:R == x.
Check n%:R != x.

End DemoCoercionsNatmul.

Section DemoCoercionsIntmul.

Variable R : numDomainType.

Variables (x : R) (n : int).

Lemma test_int : n + x + 1 = x + (n + 1)%:~R.
Proof.
(* n + x + 1 = x + (n + 1)%:~R *)
rewrite intrD.
(* n + x + 1 = x + (n%:~R + 1%:~R) *)
rewrite rmorph1.
(* n + x + 1 = x + (n%:~R + 1) *)
rewrite intz.
(* n + x + 1 = x + (n + 1) *)
by rewrite addrCA addrA.
Qed.

(* but %:~R needs to be printed on LHS of comparisons *)
Check n%:~R = x.
Check n%:~R <> x.
Check n%:~R == x.
Check n%:~R != x.
Check n%:~R <= x.
Check n%:~R < x.

End DemoCoercionsIntmul.

Section DemoCoercionsRatr.

Variable F : numFieldType.

Variables (x : F) (r : rat).

Lemma test_rat : r + x + 1 = x + ratr (r + 1).
Proof.
(* r + x + 1 = x + ratr (r + 1) *)
rewrite raddfD/=.
(* r + x + 1 = x + (ratr r + ratr 1) *)
rewrite rmorph1.
(* r + x + 1 = x + (ratr r + 1) *)
rewrite fmorph_rat.
(* r + x + 1 = x + (r + 1) *)
by rewrite addrCA addrA.
Qed.

(* but [ratr] needs to be printed on LHS of comparisons *)
Check ratr r = x.
Check ratr r <> x.
Check ratr r == x.
Check ratr r != x.
Check ratr r <= x.
Check ratr r < x.

End DemoCoercionsRatr.
