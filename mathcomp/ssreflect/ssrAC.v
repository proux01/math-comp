From HB Require Import structures.
(* use #[warning="-hiding-delimiting-key"] attribute once we require Coq 8.18 *)
Set Warnings "-hiding-delimiting-key".
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq bigop.
Set Warnings "hiding-delimiting-key".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(************************************************************************)
(*     Small Scale Rewriting using Associativity and Commutativity      *)
(*                                                                      *)
(* Rewriting with AC (not modulo AC), using a small scale command.      *)
(* Replaces opA, opC, opAC, opCA, ... and any combinations of them      *)
(*                                                                      *)
(* Usage :                                                              *)
(*   rewrite [pattern](AC patternshape reordering)                      *)
(*   rewrite [pattern](ACl reordering)                                  *)
(*   rewrite [pattern](ACof reordering reordering)                      *)
(*   rewrite [pattern]op.[AC patternshape reordering]                   *)
(*   rewrite [pattern]op.[ACl reordering]                               *)
(*   rewrite [pattern]op.[ACof reordering reordering]                   *)
(*                                                                      *)
(* - if op is specified, the rule is specialized to op                  *)
(*   otherwise,          the head symbol is a generic comm_law          *)
(*                       and the rewrite might be less efficient        *)
(*   NOTE because of a bug in Coq's notations coq/coq#8190              *)
(*        op must not contain any hole.                                 *)
(*        *%R.[AC p s] currently does not work because of that          *)
(*        (@GRing.mul R).[AC p s] must be used instead                  *)
(*                                                                      *)
(* - pattern is optional, as usual, but must be used to select the      *)
(*   appropriate operator in case of ambiguity such an operator must    *)
(*   have a canonical Monoid.com_law structure                          *)
(*   (additions, multiplications, conjuction and disjunction do)        *)
(*                                                                      *)
(* - patternshape is expressed using the syntax                         *)
(*      p := n | p * p'                                                 *)
(*      where "*" is purely formal                                      *)
(*        and n > 0 is the number of left associated symbols            *)
(*   examples of pattern shapes:                                        *)
(*   + 4 represents (n * m * p * q)                                     *)
(*   + (1*2) represents (n * (m * p))                                   *)
(*                                                                      *)
(* - reordering is expressed using the syntax                           *)
(*     s := n | s * s'                                                  *)
(*   where "*" is purely formal and n > 0 is the position in the LHS    *)
(*   positions start at 1 !                                             *)
(*                                                                      *)
(* If the ACl variant is used, the patternshape defaults to the         *)
(* pattern fully associated to the left i.e. n i.e (x * y * ...)        *)
(*                                                                      *)
(* Examples of reorderings:                                             *)
(* - ACl ((1*2)*3) is the identity (and will fail with error message)   *)
(* - opAC == op.[ACl (1*3)*2] == op.[AC 3 ((1*3)*2)]                    *)
(* - opCA == op.[AC (2*1) (1*2*3)]                                      *)
(* - opACA == op.[AC (2*2) ((1*3)*(2*4))]                               *)
(* - rewrite opAC -opA == rewrite op.[ACl 1*(3*2)]                      *)
(* ...                                                                  *)
(************************************************************************)

Declare Scope AC_scope.

Delimit Scope AC_scope with AC.

Definition change_type ty ty' (x : ty) (strategy : ty = ty') : ty' :=
 ecast ty ty strategy x.
Notation simplrefl := (ltac: (simpl; reflexivity)) (only parsing).
Notation cbvrefl := (ltac: (cbv; reflexivity)) (only parsing).
Notation vmrefl := (ltac: (vm_compute; reflexivity)) (only parsing).

(* From stdlib *)
Module Pos.

Inductive positive : Set :=
  | xI : positive -> positive
  | xO : positive -> positive
  | xH : positive.

Declare Scope positive_scope.
Delimit Scope positive_scope with positive.
Bind Scope positive_scope with positive.
Arguments xO _%positive.
Arguments xI _%positive.

Inductive N : Set :=
  | N0 : N
  | Npos : positive -> N.

Fixpoint nat_of_pos p0 :=
  match p0 with
  | xO p => (nat_of_pos p).*2
  | xI p => (nat_of_pos p).*2.+1
  | xH   => 1%N
  end.

Fixpoint pos_of_nat n0 m0 :=
  match n0, m0 with
  | n.+1, m.+2 => pos_of_nat n m
  | n.+1,    1 => xO (pos_of_nat n n)
  | n.+1,    0 => xI (pos_of_nat n n)
  |    0,    _ => xH
  end.

Definition nat_of_bin b := if b is Npos p then nat_of_pos p else 0.

Local Open Scope positive_scope.

Local Notation "1" := xH : positive_scope.
Local Notation "p ~ 1" := (xI p)
 (at level 7, left associativity, format "p '~' '1'") : positive_scope.
Local Notation "p ~ 0" := (xO p)
 (at level 7, left associativity, format "p '~' '0'") : positive_scope.

(*
Definition of_num_uint (d:Number.uint) : N :=
  match d with
  | Number.UIntDecimal d => Some (of_uint d)
  | Number.UIntHexadecimal d => None
  end.

Definition to_num_int n := Number.IntDecimal (to_int n).

Number Notation positive of_num_int to_num_uint : positive_scope.
*)

Fixpoint eqb p q {struct q} :=
  match p, q with
    | p~1, q~1 => eqb p q
    | p~0, q~0 => eqb p q
    | 1, 1 => true
    | _, _ => false
  end.

Theorem eqb_eq p q : eqb p q = true <-> p=q.
Proof.
by elim: p q => [p IHp|p IHp|] [q|q|] //=; split=> [/IHp->//|]; case=> /IHp.
Qed.

(** ** Successor *)

Fixpoint succ x :=
  match x with
    | p~1 => (succ p)~0
    | p~0 => p~1
    | 1 => 1~0
  end.

(** ** Addition *)

Fixpoint add x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~0
    | p~1, q~0 => (add p q)~1
    | p~1, 1 => (succ p)~0
    | p~0, q~1 => (add p q)~1
    | p~0, q~0 => (add p q)~0
    | p~0, 1 => p~1
    | 1, q~1 => (succ q)~0
    | 1, q~0 => q~1
    | 1, 1 => 1~0
  end

with add_carry x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~1
    | p~1, q~0 => (add_carry p q)~0
    | p~1, 1 => (succ p)~1
    | p~0, q~1 => (add_carry p q)~0
    | p~0, q~0 => (add p q)~1
    | p~0, 1 => (succ p)~0
    | 1, q~1 => (succ q)~1
    | 1, q~0 => (succ q)~0
    | 1, 1 => 1~1
  end.

(** ** Operation [x -> 2*x-1] *)

Fixpoint pred_double x :=
  match x with
    | p~1 => p~0~1
    | p~0 => (pred_double p)~1
    | 1 => 1
  end.

(** ** An auxiliary type for subtraction *)

Inductive mask : Set :=
| IsNul : mask
| IsPos : positive -> mask
| IsNeg : mask.

(** ** Operation [x -> 2*x+1] *)

Definition succ_double_mask (x:mask) : mask :=
  match x with
    | IsNul => IsPos 1
    | IsNeg => IsNeg
    | IsPos p => IsPos p~1
  end.

(** ** Operation [x -> 2*x] *)

Definition double_mask (x:mask) : mask :=
  match x with
    | IsNul => IsNul
    | IsNeg => IsNeg
    | IsPos p => IsPos p~0
  end.

(** ** Operation [x -> 2*x-2] *)

Definition double_pred_mask x : mask :=
  match x with
    | p~1 => IsPos p~0~0
    | p~0 => IsPos (pred_double p)~0
    | 1 => IsNul
  end.

(** ** Subtraction, result as a mask *)

Fixpoint sub_mask (x y:positive) {struct y} : mask :=
  match x, y with
    | p~1, q~1 => double_mask (sub_mask p q)
    | p~1, q~0 => succ_double_mask (sub_mask p q)
    | p~1, 1 => IsPos p~0
    | p~0, q~1 => succ_double_mask (sub_mask_carry p q)
    | p~0, q~0 => double_mask (sub_mask p q)
    | p~0, 1 => IsPos (pred_double p)
    | 1, 1 => IsNul
    | 1, _ => IsNeg
  end

with sub_mask_carry (x y:positive) {struct y} : mask :=
  match x, y with
    | p~1, q~1 => succ_double_mask (sub_mask_carry p q)
    | p~1, q~0 => double_mask (sub_mask p q)
    | p~1, 1 => IsPos (pred_double p)
    | p~0, q~1 => double_mask (sub_mask_carry p q)
    | p~0, q~0 => succ_double_mask (sub_mask_carry p q)
    | p~0, 1 => double_pred_mask p
    | 1, _ => IsNeg
  end.

(** ** Subtraction, result as a positive, returning 1 if [x<=y] *)

Definition sub x y :=
  match sub_mask x y with
    | IsPos z => z
    | _ => 1
  end.

(** ** Multiplication *)

Fixpoint mul x y :=
  match x with
    | p~1 => add y (mul p y)~0
    | p~0 => (mul p y)~0
    | 1 => y
  end.

(** ** Iteration over a positive number *)

Definition iter {A} (f:A -> A) : A -> positive -> A :=
  fix iter_fix x n := match n with
    | xH => f x
    | xO n' => iter_fix (iter_fix x n') n'
    | xI n' => f (iter_fix (iter_fix x n') n')
  end.

(** ** Conversion with a decimal representation for printing/parsing *)

Local Notation ten := 1~0~1~0.

Fixpoint of_uint_acc (d:Decimal.uint)(acc:positive) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 l => of_uint_acc l (mul ten acc)
  | Decimal.D1 l => of_uint_acc l (add 1 (mul ten acc))
  | Decimal.D2 l => of_uint_acc l (add 1~0 (mul ten acc))
  | Decimal.D3 l => of_uint_acc l (add 1~1 (mul ten acc))
  | Decimal.D4 l => of_uint_acc l (add 1~0~0 (mul ten acc))
  | Decimal.D5 l => of_uint_acc l (add 1~0~1 (mul ten acc))
  | Decimal.D6 l => of_uint_acc l (add 1~1~0 (mul ten acc))
  | Decimal.D7 l => of_uint_acc l (add 1~1~1 (mul ten acc))
  | Decimal.D8 l => of_uint_acc l (add 1~0~0~0 (mul ten acc))
  | Decimal.D9 l => of_uint_acc l (add 1~0~0~1 (mul ten acc))
  end.

Fixpoint of_uint (d:Decimal.uint) : N :=
  match d with
  | Decimal.Nil => N0
  | Decimal.D0 l => of_uint l
  | Decimal.D1 l => Npos (of_uint_acc l 1)
  | Decimal.D2 l => Npos (of_uint_acc l 1~0)
  | Decimal.D3 l => Npos (of_uint_acc l 1~1)
  | Decimal.D4 l => Npos (of_uint_acc l 1~0~0)
  | Decimal.D5 l => Npos (of_uint_acc l 1~0~1)
  | Decimal.D6 l => Npos (of_uint_acc l 1~1~0)
  | Decimal.D7 l => Npos (of_uint_acc l 1~1~1)
  | Decimal.D8 l => Npos (of_uint_acc l 1~0~0~0)
  | Decimal.D9 l => Npos (of_uint_acc l 1~0~0~1)
  end.

Local Notation sixteen := 1~0~0~0~0.

Fixpoint of_hex_uint_acc (d:Hexadecimal.uint)(acc:positive) :=
  match d with
  | Hexadecimal.Nil => acc
  | Hexadecimal.D0 l => of_hex_uint_acc l (mul sixteen acc)
  | Hexadecimal.D1 l => of_hex_uint_acc l (add 1 (mul sixteen acc))
  | Hexadecimal.D2 l => of_hex_uint_acc l (add 1~0 (mul sixteen acc))
  | Hexadecimal.D3 l => of_hex_uint_acc l (add 1~1 (mul sixteen acc))
  | Hexadecimal.D4 l => of_hex_uint_acc l (add 1~0~0 (mul sixteen acc))
  | Hexadecimal.D5 l => of_hex_uint_acc l (add 1~0~1 (mul sixteen acc))
  | Hexadecimal.D6 l => of_hex_uint_acc l (add 1~1~0 (mul sixteen acc))
  | Hexadecimal.D7 l => of_hex_uint_acc l (add 1~1~1 (mul sixteen acc))
  | Hexadecimal.D8 l => of_hex_uint_acc l (add 1~0~0~0 (mul sixteen acc))
  | Hexadecimal.D9 l => of_hex_uint_acc l (add 1~0~0~1 (mul sixteen acc))
  | Hexadecimal.Da l => of_hex_uint_acc l (add 1~0~1~0 (mul sixteen acc))
  | Hexadecimal.Db l => of_hex_uint_acc l (add 1~0~1~1 (mul sixteen acc))
  | Hexadecimal.Dc l => of_hex_uint_acc l (add 1~1~0~0 (mul sixteen acc))
  | Hexadecimal.Dd l => of_hex_uint_acc l (add 1~1~0~1 (mul sixteen acc))
  | Hexadecimal.De l => of_hex_uint_acc l (add 1~1~1~0 (mul sixteen acc))
  | Hexadecimal.Df l => of_hex_uint_acc l (add 1~1~1~1 (mul sixteen acc))
  end.

Fixpoint of_hex_uint (d:Hexadecimal.uint) : N :=
  match d with
  | Hexadecimal.Nil => N0
  | Hexadecimal.D0 l => of_hex_uint l
  | Hexadecimal.D1 l => Npos (of_hex_uint_acc l 1)
  | Hexadecimal.D2 l => Npos (of_hex_uint_acc l 1~0)
  | Hexadecimal.D3 l => Npos (of_hex_uint_acc l 1~1)
  | Hexadecimal.D4 l => Npos (of_hex_uint_acc l 1~0~0)
  | Hexadecimal.D5 l => Npos (of_hex_uint_acc l 1~0~1)
  | Hexadecimal.D6 l => Npos (of_hex_uint_acc l 1~1~0)
  | Hexadecimal.D7 l => Npos (of_hex_uint_acc l 1~1~1)
  | Hexadecimal.D8 l => Npos (of_hex_uint_acc l 1~0~0~0)
  | Hexadecimal.D9 l => Npos (of_hex_uint_acc l 1~0~0~1)
  | Hexadecimal.Da l => Npos (of_hex_uint_acc l 1~0~1~0)
  | Hexadecimal.Db l => Npos (of_hex_uint_acc l 1~0~1~1)
  | Hexadecimal.Dc l => Npos (of_hex_uint_acc l 1~1~0~0)
  | Hexadecimal.Dd l => Npos (of_hex_uint_acc l 1~1~0~1)
  | Hexadecimal.De l => Npos (of_hex_uint_acc l 1~1~1~0)
  | Hexadecimal.Df l => Npos (of_hex_uint_acc l 1~1~1~1)
  end.

Definition of_int (d:Decimal.int) : option positive :=
  match d with
  | Decimal.Pos d =>
    match of_uint d with
    | N0 => None
    | Npos p => Some p
    end
  | Decimal.Neg _ => None
  end.

Definition of_hex_int (d:Hexadecimal.int) : option positive :=
  match d with
  | Hexadecimal.Pos d =>
    match of_hex_uint d with
    | N0 => None
    | Npos p => Some p
    end
  | Hexadecimal.Neg _ => None
  end.

Definition of_num_int (d:Number.int) : option positive :=
  match d with
  | Number.IntDecimal d => of_int d
  | Number.IntHexadecimal d => of_hex_int d
  end.

Fixpoint to_little_uint p :=
  match p with
  | 1 => Decimal.D1 Decimal.Nil
  | p~1 => Decimal.Little.succ_double (to_little_uint p)
  | p~0 => Decimal.Little.double (to_little_uint p)
  end.

Definition to_uint p := Decimal.rev (to_little_uint p).

Definition to_num_uint p := Number.UIntDecimal (to_uint p).

(** ** Successor *)

Definition Nsucc n :=
  match n with
  | N0 => Npos xH
  | Npos p => Npos (Pos.succ p)
  end.

Lemma nat_of_succ_bin b : nat_of_bin (Nsucc b) = 1 + nat_of_bin b :> nat.
Proof. by case: b => [//|p /=]; elim: p => // p /= ->. Qed.

End Pos.

Module AC.

HB.instance Definition _ := hasDecEq.Build Pos.positive
  (fun _ _ => equivP idP (Pos.eqb_eq _ _)).

Inductive syntax := Leaf of Pos.positive | Op of syntax & syntax.
Coercion serial := (fix loop (acc : seq Pos.positive) (s : syntax) :=
   match s with
   | Leaf n => n :: acc
   | Op s s' => (loop^~ s (loop^~ s' acc))
   end) [::].

Lemma serial_Op s1 s2 : Op s1 s2 = s1 ++ s2 :> seq _.
Proof.
rewrite /serial; set loop := (X in X [::]); rewrite -/loop.
elim: s1 (loop [::] s2) => [n|s11 IHs1 s12 IHs2] //= l.
by rewrite IHs1 [in RHS]IHs1 IHs2 catA.
Qed.

Definition Leaf_of_nat n := Leaf (Pos.sub (Pos.pos_of_nat n n) Pos.xH).

Module Import Syntax.
Bind Scope AC_scope with syntax.
Number Notation Pos.positive Pos.of_num_int Pos.to_num_uint : AC_scope.
Coercion Leaf : Pos.positive >-> syntax.
Coercion Leaf_of_nat : nat >-> syntax.
Notation "x * y" := (Op x%AC y%AC) : AC_scope.
End Syntax.

Definition pattern (s : syntax) := ((fix loop n s :=
  match s with
  | Leaf Pos.xH => (Leaf n, Pos.succ n)
  | Leaf m => Pos.iter (fun oi => (Op oi.1 (Leaf oi.2), Pos.succ oi.2))
                       (Leaf n, Pos.succ n) (Pos.sub m Pos.xH)
  | Op s s' => let: (p, n') := loop n s in
               let: (p', n'') := loop n' s' in
               (Op p p', n'')
  end) Pos.xH s).1.

Section eval.
Variables (T : Type) (idx : T) (op : T -> T -> T).
Inductive env := Empty | ENode of T & env & env.
Definition pos := fix loop (e : env) p {struct e} :=
  match e, p with
 | ENode t _ _, Pos.xH => t
 | ENode t e _, Pos.xO p => loop e p
 | ENode t _ e, Pos.xI p => loop e p
 | _, _ => idx
end.

Definition set_pos (f : T -> T) := fix loop e p {struct p} :=
  match e, p with
 | ENode t e e', Pos.xH => ENode (f t) e e'
 | ENode t e e', Pos.xO p => ENode t (loop e p) e'
 | ENode t e e', Pos.xI p => ENode t e (loop e' p)
 | Empty, Pos.xH => ENode (f idx) Empty Empty
 | Empty, Pos.xO p => ENode idx (loop Empty p) Empty
 | Empty, Pos.xI p => ENode idx Empty (loop Empty p)
 end.

Lemma pos_set_pos (f : T -> T) e (p p' : Pos.positive) :
  pos (set_pos f e p) p' = if p == p' then f (pos e p) else pos e p'.
Proof. by elim: p e p' => [p IHp|p IHp|] [|???] [?|?|]//=; rewrite IHp. Qed.

Fixpoint unzip z (e : env) : env := match z with
 | [::] => e
 | (x, inl e') :: z' => unzip z' (ENode x e' e)
 | (x, inr e') :: z' => unzip z' (ENode x e e')
end.

Definition set_pos_trec (f : T -> T) := fix loop z e p {struct p} :=
  match e, p with
 | ENode t e e', Pos.xH => unzip z (ENode (f t) e e')
 | ENode t e e', Pos.xO p => loop ((t, inr e') :: z) e p
 | ENode t e e', Pos.xI p => loop ((t, inl e) :: z) e' p
 | Empty, Pos.xH => unzip z (ENode (f idx) Empty Empty)
 | Empty, Pos.xO p => loop ((idx, (inr Empty)) :: z) Empty p
 | Empty, Pos.xI p => loop ((idx, (inl Empty)) :: z) Empty p
 end.

Lemma set_pos_trecE f z e p : set_pos_trec f z e p = unzip z (set_pos f e p).
Proof. by elim: p e z => [p IHp|p IHp|] [|???] [|[??]?] //=; rewrite ?IHp. Qed.

Definition eval (e : env) := fix loop (s : syntax) :=
match s with
  | Leaf n => pos e n
  | Op s s' => op (loop s) (loop s')
end.
End eval.
Arguments Empty {T}.

Definition content := (fix loop (acc : env Pos.N) s :=
  match s with
  | Leaf n => set_pos_trec Pos.N0 Pos.Nsucc [::] acc n
  | Op s s' => loop (loop acc s') s
  end) Empty.

Lemma count_memE x (t : syntax) :
  count_mem x t = Pos.nat_of_bin (pos Pos.N0 (content t) x).
Proof.
rewrite /content; set loop := (X in X Empty); rewrite -/loop.
rewrite -[LHS]addn0.
have <- : Pos.nat_of_bin (pos Pos.N0 Empty x) = 0 :> nat by elim: x.
elim: t Empty => [n|s IHs s' IHs'] e //=; last first.
  by rewrite serial_Op count_cat -addnA IHs' IHs.
rewrite ?addn0 set_pos_trecE pos_set_pos; case: (altP eqP) => [->|] //=.
by rewrite Pos.nat_of_succ_bin.
Qed.

Definition cforall N T : env N -> (env T -> Type) -> Type := env_rect (@^~ Empty)
  (fun _ e IHe e' IHe' R => forall x, IHe (fun xe => IHe' (R \o ENode x xe))).

Lemma cforallP N T R : (forall e : env T, R e) -> forall (e : env N), cforall e R.
Proof.
move=> Re e; elim: e R Re => [|? e /= IHe e' IHe' ?? x] //=.
by apply: IHe => ?; apply: IHe' => /=.
Qed.

Section eq_eval.
Variables (T : Type) (idx : T) (op : Monoid.com_law idx).

Lemma proof (p s : syntax) : content p = content s ->
  forall env, eval idx op env p = eval idx op env s.
Proof.
suff evalE env t : eval idx op env t = \big[op/idx]_(i <- t) (pos idx env i).
  move=> cps e; rewrite !evalE; apply: perm_big.
  by apply/allP => x _ /=; rewrite !count_memE cps.
elim: t => //= [n|t -> t' ->]; last by rewrite serial_Op big_cat.
by rewrite big_cons big_nil Monoid.mulm1.
Qed.

Definition direct p s ps := cforallP (@proof p s ps) (content p).

End eq_eval.

Module Exports.
Export AC.Syntax.
End Exports.
End AC.
Export AC.Exports.

Notation AC_check_pattern :=
  (ltac: (match goal with
    |- AC.content ?pat = AC.content ?ord =>
      let pat' := fresh "pat" in let pat' := eval compute in pat in
      tryif unify pat' ord then
           fail 1 "AC: equality between" pat
                  "and" ord "is trivial, cannot progress"
      else tryif vm_compute; reflexivity then idtac
      else fail 2 "AC: mismatch between shape" pat "=" pat' "and reordering" ord
    | |- ?G => fail 3 "AC: no pattern to check" G
  end))
  (only parsing).

Notation opACof law p s :=
((fun T idx op assoc lid rid comm => (change_type (@AC.direct T idx
   (Monoid.ComLaw.Pack  (* FIXME: find a way to make this robust to hierarchy evolutions *)
      (Monoid.ComLaw.Class
         (SemiGroup.isLaw.Axioms_ op assoc)
         (Monoid.isMonoidLaw.Axioms_ idx op lid rid)
         (SemiGroup.isCommutativeLaw.Axioms_ op comm)))
   p%AC s%AC AC_check_pattern) cbvrefl)) _ _ law
(Monoid.mulmA _) (Monoid.mul1m _) (Monoid.mulm1 _) (Monoid.mulmC _))
(only parsing).

Notation opAC op  p s := (opACof op (AC.pattern p%AC) s%AC) (only parsing).
Notation opACl op s := (opAC op (AC.Leaf_of_nat (size (AC.serial s%AC))) s%AC)
  (only parsing).

Notation "op .[ 'ACof' p s ]" := (opACof op p%AC s%AC)
  (at level 2, p at level 1, left associativity, only parsing).
Notation "op .[ 'AC' p s ]" := (opAC op p%AC s%AC)
  (at level 2, p at level 1, left associativity, only parsing).
Notation "op .[ 'ACl' s ]" := (opACl op s%AC)
  (at level 2, left associativity, only parsing).

Notation AC_strategy :=
  (ltac: (cbv -[Monoid.ComLaw.sort Monoid.Law.sort]; reflexivity))
  (only parsing).
Notation ACof p s := (change_type
  (@AC.direct _ _ _  p%AC s%AC AC_check_pattern) AC_strategy)
  (only parsing).
Notation AC p s := (ACof (AC.pattern p%AC) s%AC) (only parsing).
Notation ACl s := (AC (AC.Leaf_of_nat (size (AC.serial s%AC))) s%AC)
  (only parsing).
