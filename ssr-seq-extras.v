(* (c) GAD and the IMDEA Software Institute*)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

(******************************************************************************)
(* Several lemmas about lists that are nowherere to be found in the latest    *)
(* ssr libraries. They might end up in some HTT/ HTTcc /FCSL bundle:          *)
(*                                                                            *) 
(* Some conventions on names, extending those on seq.v and/or ssrnat.v:       *) 
(*                                                                            *) 
(*  SW - interchange for unary operation e.g. dropI :                         *)
(*              drop i (drop j xs) =  drop (i + j) xs.                        *)
(*                                                                            *) 
(******************************************************************************)

Section Surgery.
Variable (A: Type).
Implicit Types (i j : nat) (ls rs xs: seq A). 

Lemma dropA i j xs : drop i (drop j xs) =  drop (i + j) xs.
Proof.
by elim:xs i j=>//=xx ss IH [|si] [|sj]; rewrite ?drop0 ?addn0 // IH addnS.
Qed.

Lemma dropSW i j xs : drop i (drop j xs) =  drop j (drop i xs).
Proof. by rewrite !dropA [j + i]addnC. Qed.

Lemma takeM i j xs : take i (take j xs) = take (minn i j) xs.
Proof.
by elim:xs i j=>//= x xs IH [|i] [|j]//=;rewrite IH /minn ltnS; case:ifP.
Qed.

Lemma takenn i xs: take i (take i xs) = take i xs.
Proof. by rewrite takeM /minn ltnn. Qed.

Lemma take_drop i j xs : take i (drop j xs) = drop j (take (i + j) xs).
Proof.
elim:xs i j=>//=x xs IH [|i][|j]//=; rewrite ?IH ?add0n //= ?addSn -?addnS //.
by rewrite -{1}[xs](@drop0 _ xs) IH drop0.
Qed.  

Lemma drop_take i j xs :
       drop i (take j xs) = if i < j then take (j - i) (drop i xs) else [::].
Proof.
elim:xs i j=>//=[|x xs IH ] i j;first by rewrite if_same. 
case: i j =>//=[|i][|j]; rewrite ?drop0 ?subn0 //=.
by rewrite ?ltnS ?leq0n ?lt0n IH //.
Qed.  

End Surgery.

