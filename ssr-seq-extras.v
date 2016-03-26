(* (c) GAD and the IMDEA Software Institute*)
(* You may distribute this file under the terms of the CeCILL-B license *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.

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

Section Indexes.
Implicit Type (T : eqType).

Lemma uniq_last_index {T} n0 (s: seq T) :
       uniq s -> index (last n0 s) s = (size s).-1.
Proof.
elim/last_ind:s=>//s t _.
rewrite last_rcons  size_rcons rcons_uniq -cats1 index_cat /=. 
case/andP=>/negP H U; case:ifP=>//_; rewrite eq_refl addn0 //.
Qed.
End Indexes.

Section Filtering.
Variable (A: Type).
Lemma filter0 (r: seq A) : @filter A xpred0 r = [::].
Proof. by elim:r. Qed.

Lemma filterT (r: seq A) : @filter A xpredT r = r.
Proof. by elim:r=>//= a l ->. Qed.

Lemma uniq_perm_filter {T:eqType} p (r s: seq T): 
       uniq r -> perm_eq r s -> perm_eq (filter p r) (filter p s).
Proof.
move=> US E.
move:(perm_eq_uniq E) (US)=>-> UR.
apply:uniq_perm_eq; try by rewrite  filter_uniq //. 
by move=>x ; rewrite !mem_filter (perm_eq_mem E).
Qed.
End Filtering.

Section SurgeryLemmas.

Section Algebra.
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

(* all_surgery *)

Lemma all_drop p i xs: all p xs -> all p (drop i xs).
Proof. by rewrite -{1}(cat_take_drop i xs) all_cat; case/andP=>_->. Qed.

Lemma all_take p i xs: all p xs -> all p (take i xs).
Proof. by rewrite -{1}(cat_take_drop i xs) all_cat; case/andP=>->. Qed.

(* uniq_surgery *)

Lemma uniq_drop  {T: eqType} i (rs: seq T): uniq rs -> uniq (drop i rs).
Proof. by rewrite -{1}(cat_take_drop i rs) cat_uniq; case/and3P=>[_] _ ->. Qed.

Lemma uniq_take  {T: eqType} i (rs: seq T): uniq rs -> uniq (take i rs).
Proof. by rewrite -{1}(cat_take_drop i rs) cat_uniq; case/and3P=>->. Qed.

End Algebra.

Section MemSurgeryLemmas.
Variable T: eqType.
Implicit Types (t: T) (xs ls rs : seq T).  

Lemma drop_index c rs:
       c \in rs -> drop (index c rs) rs = c :: drop (index c rs).+1 rs.
Proof. by move=> C; rewrite (@drop_nth _ c _ _ ) ?index_mem // nth_index. Qed.

(* membership wr.t. take and drop *)
Lemma mem_dropW t j k rs:
        k <= j -> t \in drop j rs -> t \in drop k rs.
Proof. by move=>W; rewrite -[j](subnK W) -dropA => /mem_drop //. Qed.

Lemma mem_takeW t j k (rs: seq T):
        k <= j -> t \in take k rs -> t \in take j rs.
Proof.
by move=>W; rewrite -[k](subKn W) -minnE minnC -takeM=> /mem_take. Qed.

Lemma mem_take_self k rs: k \notin take (index k rs) rs.
Proof.
by elim:rs=>//= a l IH; case:eqP=>//; rewrite in_cons negb_or IH =>/nesym/eqP->.
Qed.

Lemma mem_drop_self k rs: k \in drop (index k rs) rs = (k \in rs).
Proof. by elim:rs=>//= a l IH; case:ifP=>//; rewrite in_cons IH eq_sym=>->. Qed.

Lemma mem_drop_selfS k rs: uniq rs -> k \notin (drop (index k rs).+1 rs).
Proof.
by elim:rs=>//= a l IH /andP[N]/IH{IH}IH; case:eqP=>//= <-; rewrite drop0 N //.
Qed.  

Lemma mem_take_index t k rs:
        t \in take (index k rs) rs = (index t rs < index k rs).
Proof.
by elim:rs=>//= a l IH; case:eqP=>//; rewrite in_cons eq_sym IH; case:eqP=>//.
Qed.

Lemma index_take t k rs:
        index t (take k rs) = if (index t rs) <= k then index t rs
                              else size (take k rs).
Proof.
elim: k rs=>//= [|n IH] rs; first by rewrite take0 //= leqn0; case:eqP=>//.
case:rs=>//a ls /=.
by case:eqP=>// E; rewrite IH ltnS; case:ifP=>//.
Qed.

Lemma index_drop_uniq t k rs:
      uniq rs -> index t (drop k rs) = if (index t rs) < k then size (drop k rs)
                                       else if (size rs <= k) then 0
                                            else index t rs - k.
Proof.
elim:rs k=>//[|a l IH ][]//=; first by rewrite subn0.
move=>n /andP[A]/IH{IH} IH; rewrite ltnS IH; case:eqP=>//=E.
do 2 case:ifP=>//; move=>P1 P2; first by rewrite drop_oversize //.
rewrite size_drop.
rewrite E -index_mem ltn_neqAle negb_and (index_size t l) orbF /= in A.
by case:(@eqP _ (index t l) (size l)) A=>[->|/eqP]//.
Qed.

Lemma mem_drop_index t k rs:
      uniq rs -> t \in drop (index k rs) rs -> index k rs <= index t rs.
Proof.
elim rs=>//= [a]l IH /andP[/negP N]/IH{IH}IH.
case:eqP=>E; rewrite eq_sym ?in_cons -?E; case:eqP=>//= -> /mem_drop/N//.
Qed.


Lemma mem_take_ltn a n rs:
         (a \in take n rs) -> (index a rs < n).
Proof.
elim:n rs=>[|n IH]s; first by rewrite take0 //.
case:s=>//= r s; rewrite in_cons eq_sym.
case/orP=>[/eqP ->|]; rewrite ?eq_refl // ltnS.
by case:eqP=>//_ /IH.
Qed.

Lemma mem_drop_ltn a n rs:
       uniq rs -> (a \in drop n rs) -> (index a rs >= n).
Proof.
elim:n rs=>[|n IH]s; first by rewrite drop0 //.
case:s=>//= r s.
case:eqP=>//[->|_]/andP[/negP R]U; first by move/mem_drop.
by apply:IH.
Qed.
End MemSurgeryLemmas.

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
Proof. by rewrite -(@perm_eq_uniq _ s) // perm_swap. Qed.

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
       many p s ->  exists tc, exists ss, [/\ p tc, all p ss & s = tc :: ss].
Proof. by case:s=>//= tc s /andP [P] H2; exists tc, s. Qed.

Lemma all_perm_eq (T : eqType) p (r s : seq T):
       perm_eq r s -> all p r -> all p s. 
Proof.
move/perm_eq_mem =>RS /allP R; case:allP=>// S.
by apply:False_ind; apply:S=> x; rewrite -RS=> /R.
Qed.

End AMULemmas.
End AMU.