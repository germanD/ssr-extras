(* (c) GAD and th IMDEA Software Institute*)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.

(******************************************************************************)
(* Several lemmas about lists that are nowherere to be found in the latest    *)
(* ssr libraries. They might end up in some HTT/ HTTcc /FCSL bundle           *) 
(******************************************************************************)

Section Surgery.
Variable (A: Type).
Implicit Types (i j : nat) (ls rs xs: seq A). 

Lemma drop_dropA i j xs : drop i (drop j xs) =  drop (i + j) xs.
Proof.
by elim:xs i j=>//=xx ss IH [|si] [|sj]; rewrite ?drop0 ?addn0 // IH addnS.
Qed.

Lemma drop_dropI i j xs : drop i (drop j xs) =  drop j (drop i xs).
Proof. by rewrite !drop_dropA [j + i]addnC. Qed.

End Surgery.