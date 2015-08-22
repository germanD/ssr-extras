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

Section SurgeryLemmas.
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

End SurgeryLemmas.

Section Swap.
(* Swapping the ith adn i.+1th elements of a list*) 

Definition swap {A} i (xs : seq A) :=
           let jis := if drop i xs is ti :: tj ::ss  then (tj :: ti :: ss)
                            else (drop i xs)
           in take i xs ++ jis.

Section Lemmas.
Variable (A: eqType).
Implicit Types (i : nat) (ls rs xs: seq A). 

Lemma swap_nil i: swap i (@nil A) = [::].
Proof. by rewrite /swap //. Qed.

Lemma swap_cons i l (s : seq A) :
      swap i (l :: s)  = if s is (t :: ts)
                         then if i is (S j) then l :: swap j s
                              else t :: l :: ts 
                         else l :: s.
Proof. by rewrite /swap !take_cons !drop_cons;  case:i=>//n; case:s=>//. Qed.

Lemma perm_swap {i} (s: seq A) : perm_eq s (swap i s).
Proof.
rewrite /swap -{1}(cat_take_drop i s) perm_cat2l; case:(drop i s)=>//a[|l r]//=.
by rewrite -2!(cat1s _ r) -!cat_cons perm_cat2r -cat1s
           -[in y in perm_eq _ y]cat1s perm_catC //.
Qed.

Lemma swap_uniq { i} (s : seq A): uniq s -> uniq (swap i s).
Proof. by rewrite -(@perm_eq_uniq _ s) // perm_swap.Qed.

End Lemmas.
End Swap.

Section AMU.
Variable (A: Type).
Implicit Types (i j : nat) (s ss: seq A). 

Definition many p s := if s is tc :: sss then p tc && all p sss else false.

Definition one p s :=
           match s with
             | [::] => true
             | [:: tc ] => p tc
             | _ :: ss => false
           end.

Section AMULemmas.

Lemma many_all p s: many p s -> all p s.
Proof. by case: s=>//=[[|tc s]//]. Qed.

Lemma one_all p s: one p s -> all p s.
Proof. by case: s=>//=[tc][|s]//=->//. Qed.

Lemma oneE p s: one p s <-> s = [::] \/ exists xs, s = [:: xs] /\ p xs.
Proof.
split=>//; last by case=>[->|[xs][->]P]//.
by case: s=>[|xs ss]/=; first (by left); case: ss=>//= H; right; exists xs.
Qed.

Lemma many_cons p tc s:  many p ( tc :: s)  = p tc &&  all p s.
Proof. by done. Qed.

Lemma many_rcons p tc s: many p (rcons s tc) = all p s && p tc.
Proof. by case:s=>//=[|s wv]; rewrite ?andbT // all_rcons andbAC andbA //. Qed.

Lemma many_cat p r s : many p r -> many p s -> many p (r ++ s).
Proof.
by case: r=>//tr rr; rewrite cat_cons /= all_cat=>/andP[->]-> /many_all.
Qed.                                                    

Lemma manyNE p s:
  many p s ->  exists tc, exists ss, [/\ p tc,  all p ss & s = tc :: ss].
Proof. by case:s=>//= tc s /andP [P] H2; exists tc, s. Qed.

End AMULemmas.
End AMU.